import ErdosProblems.Erdos1166.Erdos1166HLOZUrn
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Dist
import Mathlib.Analysis.Real.Pi.Wallis

/-!
# A quantitative local bound for the Appendix-A urn transition

Appendix A of Hao--Li--Okada--Zheng uses a negative-binomial law different from
the `15 / 16` law in `Erdos1166HLOZUrn`.  Conditional on `b` upcrossings at one
level, the number at the next level is a sum of `b` geometric random variables
with success probability `1 / 2`.  Its mass function is

`choose (b + b' - 1) b' / 2 ^ (b + b')`.

This file proves the elementary analytic core of the local-limit estimate used
in Proposition A.7.  Its sharp form has normalization
`1 / (2 * sqrt (πb))`, leading exponent `dist(b,b')² / (4b)`, and the explicit
remainder `3d/b + 4d³/b² + 1/b`.  These constants are retained because the
leading coefficient is what yields the source's `exp (-2n + o(n))` trajectory
scale near `b_ℓ = 2ℓ²`.
-/

open scoped BigOperators

namespace Erdos1166.HLOZAppendixA

/-- The transition mass in Remark A.5 of Hao--Li--Okada--Zheng. -/
noncomputable def halfNegBinMass (b b' : ℕ) : ℝ :=
  (Nat.choose (b + b' - 1) b' : ℝ) / (2 : ℝ) ^ (b + b')

theorem halfNegBinMass_nonneg (b b' : ℕ) : 0 ≤ halfNegBinMass b b' := by
  unfold halfNegBinMass
  positivity

theorem halfNegBinMass_pos {b b' : ℕ} (hb : 0 < b) : 0 < halfNegBinMass b b' := by
  unfold halfNegBinMass
  have hc : 0 < Nat.choose (b + b' - 1) b' := Nat.choose_pos (by omega)
  exact div_pos (by exact_mod_cast hc) (by positivity)

/-- Division-free adjacent-mass recurrence for the success-`1 / 2` law. -/
theorem halfNegBinMass_adjacent (b j : ℕ) (hb : 0 < b) :
    2 * (j + 1) * halfNegBinMass b (j + 1) =
      (b + j) * halfNegBinMass b j := by
  unfold halfNegBinMass
  push_cast
  rw [show b + (j + 1) - 1 = (b + j - 1) + 1 by omega,
    show b + (j + 1) = (b + j) + 1 by omega, pow_succ]
  have hchoose := Nat.add_one_mul_choose_eq (b + j - 1) j
  have hbjsum : b + j - 1 + 1 = b + j := by omega
  rw [hbjsum] at hchoose
  field_simp
  norm_num
  have hfinal :
      (j + 1) * Nat.choose (b + j - 1 + 1) (j + 1) =
        (b + j) * Nat.choose (b + j - 1) j := by
    simpa [hbjsum, mul_comm] using hchoose.symm
  exact_mod_cast hfinal

/-- The central binomial probability, isolated for the induction below. -/
noncomputable def centralMass (n : ℕ) : ℝ :=
  (Nat.centralBinom n : ℝ) / (4 : ℝ) ^ n

theorem centralMass_zero : centralMass 0 = 1 := by
  norm_num [centralMass, Nat.centralBinom_zero]

theorem centralMass_succ (n : ℕ) :
    centralMass (n + 1) =
      ((2 * n + 1 : ℕ) : ℝ) / (2 * (n + 1 : ℕ) : ℝ) * centralMass n := by
  have h := Nat.succ_mul_centralBinom_succ n
  have hr :
      ((n + 1 : ℕ) : ℝ) * (Nat.centralBinom (n + 1) : ℝ) =
        2 * ((2 * n + 1 : ℕ) : ℝ) * (Nat.centralBinom n : ℝ) := by
    exact_mod_cast h
  unfold centralMass
  push_cast at hr ⊢
  rw [pow_succ]
  norm_num at hr ⊢
  field_simp
  nlinarith [hr]

/-- A Wallis-strength lower bound, with a safe constant, proved elementarily
from the exact recurrence of the central binomial coefficients. -/
theorem centralMass_lower : ∀ n : ℕ, 0 < n →
    1 / (2 * Real.sqrt (n : ℝ)) ≤ centralMass n := by
  intro n hn
  induction n using Nat.case_strong_induction_on with
  | hz => omega
  | hi n ih =>
      by_cases hn0 : n = 0
      · subst n
        norm_num [centralMass, Nat.centralBinom]
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        have hsqrtn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by positivity)
        have hsqrtn1 : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) :=
          Real.sqrt_pos.2 (by positivity)
        have hsquare :
            (2 * ((n + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)) ^ 2 ≤
              (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt ((n + 1 : ℕ) : ℝ)) ^ 2 := by
          push_cast
          have hsn : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) :=
            Real.sq_sqrt (by positivity)
          have hsn1 : Real.sqrt ((n : ℝ) + 1) ^ 2 = (n : ℝ) + 1 :=
            Real.sq_sqrt (by positivity)
          calc
            (2 * ((n : ℝ) + 1) * Real.sqrt (n : ℝ)) ^ 2 =
                (2 * ((n : ℝ) + 1)) ^ 2 * Real.sqrt (n : ℝ) ^ 2 := by ring
            _ = (2 * ((n : ℝ) + 1)) ^ 2 * (n : ℝ) := by rw [hsn]
            _ ≤ (2 * (n : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) := by nlinarith
            _ = (2 * (n : ℝ) + 1) ^ 2 * Real.sqrt ((n : ℝ) + 1) ^ 2 := by rw [hsn1]
            _ = ((2 * (n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1)) ^ 2 := by ring
        have hroot :
            2 * ((n + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ) ≤
              ((2 * n + 1 : ℕ) : ℝ) * Real.sqrt ((n + 1 : ℕ) : ℝ) := by
          exact le_of_sq_le_sq hsquare (by positivity)
        have hfactor :
            1 / (2 * Real.sqrt (((n + 1 : ℕ) : ℝ))) ≤
              (((2 * n + 1 : ℕ) : ℝ) / (2 * ((n + 1 : ℕ) : ℝ))) *
                (1 / (2 * Real.sqrt (n : ℝ))) := by
          rw [div_mul_div_comm]
          apply (div_le_div_iff₀ (by positivity) (by positivity)).2
          nlinarith
        rw [centralMass_succ]
        exact hfactor.trans (mul_le_mul_of_nonneg_left (ih n (by omega) hnpos) (by positivity))

/-- A matching-order upper bound for the central mass. -/
theorem centralMass_upper : ∀ n : ℕ,
    centralMass n ≤ 1 / Real.sqrt ((n + 1 : ℕ) : ℝ) := by
  intro n
  induction n with
  | zero => norm_num [centralMass_zero]
  | succ n ih =>
      have hsqrtn1 : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) :=
        Real.sqrt_pos.2 (by positivity)
      have hsqrtn2 : 0 < Real.sqrt ((n + 2 : ℕ) : ℝ) :=
        Real.sqrt_pos.2 (by positivity)
      have hsquare :
          (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt ((n + 2 : ℕ) : ℝ)) ^ 2 ≤
            (2 * ((n + 1 : ℕ) : ℝ) * Real.sqrt ((n + 1 : ℕ) : ℝ)) ^ 2 := by
        push_cast
        have hsn1 : Real.sqrt ((n : ℝ) + 1) ^ 2 = (n : ℝ) + 1 :=
          Real.sq_sqrt (by positivity)
        have hsn2 : Real.sqrt ((n : ℝ) + 2) ^ 2 = (n : ℝ) + 2 :=
          Real.sq_sqrt (by positivity)
        calc
          ((2 * (n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 2)) ^ 2 =
              (2 * (n : ℝ) + 1) ^ 2 * Real.sqrt ((n : ℝ) + 2) ^ 2 := by ring
          _ = (2 * (n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2) := by rw [hsn2]
          _ ≤ (2 * ((n : ℝ) + 1)) ^ 2 * ((n : ℝ) + 1) := by nlinarith
          _ = (2 * ((n : ℝ) + 1)) ^ 2 * Real.sqrt ((n : ℝ) + 1) ^ 2 := by rw [hsn1]
          _ = (2 * ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1)) ^ 2 := by ring
      have hroot :
          ((2 * n + 1 : ℕ) : ℝ) * Real.sqrt ((n + 2 : ℕ) : ℝ) ≤
            2 * ((n + 1 : ℕ) : ℝ) * Real.sqrt ((n + 1 : ℕ) : ℝ) := by
        exact le_of_sq_le_sq hsquare (by positivity)
      rw [centralMass_succ]
      calc
        _ ≤ (((2 * n + 1 : ℕ) : ℝ) / (2 * ((n + 1 : ℕ) : ℝ))) *
              (1 / Real.sqrt ((n + 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left ih (by positivity)
        _ ≤ 1 / Real.sqrt ((n + 2 : ℕ) : ℝ) := by
          rw [div_mul_div_comm]
          apply (div_le_div_iff₀ (by positivity)
            (by positivity : (0 : ℝ) < Real.sqrt ((n + 2 : ℕ) : ℝ))).2
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hroot

/-- Exact Wallis-product identity for the normalized central coefficient. -/
theorem wallis_mul_centralMass_sq (n : ℕ) :
    Real.Wallis.W n * centralMass n ^ 2 * (2 * (n : ℝ) + 1) = 1 := by
  have hcNat := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
  rw [show 2 * n - n = n by omega] at hcNat
  have hc :
      (Nat.centralBinom n : ℝ) * (n.factorial : ℝ) * (n.factorial : ℝ) =
        ((2 * n).factorial : ℝ) := by
    rw [Nat.centralBinom_eq_two_mul_choose]
    exact_mod_cast hcNat
  rw [Real.Wallis.W_eq_factorial_ratio]
  unfold centralMass
  push_cast
  have hnfac : (n.factorial : ℝ) ≠ 0 := by positivity
  have h2nfac : ((2 * n).factorial : ℝ) ≠ 0 := by positivity
  have hfour : (4 : ℝ) ^ n ≠ 0 := by positivity
  have hpow : (2 : ℝ) ^ (4 * n) = ((4 : ℝ) ^ n) ^ 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul, ← pow_mul]
    congr 1
    omega
  have hcf :
      (Nat.centralBinom n : ℝ) ^ 2 * (n.factorial : ℝ) ^ 4 =
        ((2 * n).factorial : ℝ) ^ 2 := by
    calc
      _ = ((Nat.centralBinom n : ℝ) * (n.factorial : ℝ) *
          (n.factorial : ℝ)) ^ 2 := by ring
      _ = _ := congrArg (fun x : ℝ ↦ x ^ 2) hc
  field_simp [hnfac, h2nfac, hfour]
  rw [hpow]
  calc
    ((4 : ℝ) ^ n) ^ 2 * (n.factorial : ℝ) ^ 4 *
        (Nat.centralBinom n : ℝ) ^ 2 =
      ((4 : ℝ) ^ n) ^ 2 *
        ((Nat.centralBinom n : ℝ) ^ 2 * (n.factorial : ℝ) ^ 4) := by ring
    _ = ((4 : ℝ) ^ n) ^ 2 * ((2 * n).factorial : ℝ) ^ 2 := by rw [hcf]
    _ = ((2 * n).factorial : ℝ) ^ 2 * ((4 : ℝ) ^ n) ^ 2 := by ring

theorem centralMass_nonneg (n : ℕ) : 0 ≤ centralMass n := by
  unfold centralMass
  positivity

/-- Sharp Wallis lower bound for the central binomial probability. -/
theorem one_div_sqrt_pi_mul_add_half_le_centralMass (n : ℕ) :
    1 / Real.sqrt (Real.pi * ((n : ℝ) + 1 / 2)) ≤ centralMass n := by
  let X : ℝ := Real.pi * ((n : ℝ) + 1 / 2)
  have hX : 0 < X := by dsimp [X]; positivity
  have hW := Real.Wallis.W_le n
  have hden : Real.Wallis.W n * (2 * (n : ℝ) + 1) ≤ X := by
    dsimp [X]
    have hfac : (0 : ℝ) ≤ 2 * n + 1 := by positivity
    calc
      Real.Wallis.W n * (2 * (n : ℝ) + 1) ≤
          (Real.pi / 2) * (2 * (n : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right hW hfac
      _ = Real.pi * ((n : ℝ) + 1 / 2) := by ring
  have hone :
      1 ≤ centralMass n ^ 2 * X := by
    calc
      1 = centralMass n ^ 2 *
          (Real.Wallis.W n * (2 * (n : ℝ) + 1)) := by
        calc
          1 = Real.Wallis.W n * centralMass n ^ 2 *
              (2 * (n : ℝ) + 1) := (wallis_mul_centralMass_sq n).symm
          _ = _ := by ring
      _ ≤ centralMass n ^ 2 * X :=
        mul_le_mul_of_nonneg_left hden (sq_nonneg _)
  have hsqrtX : 0 < Real.sqrt X := Real.sqrt_pos.2 hX
  have hsq : (1 / Real.sqrt X) ^ 2 ≤ centralMass n ^ 2 := by
    rw [div_pow, one_pow, Real.sq_sqrt hX.le]
    exact (div_le_iff₀ hX).2 (by simpa [mul_comm] using hone)
  exact le_of_sq_le_sq hsq (centralMass_nonneg n)

theorem centralBinom_succ_as_double (n : ℕ) :
    Nat.centralBinom (n + 1) = 2 * Nat.choose (2 * n + 1) (n + 1) := by
  rw [Nat.centralBinom_eq_two_mul_choose]
  rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
    Nat.choose_succ_succ']
  rw [← Nat.choose_symm_half n]
  omega

theorem halfNegBinMass_self {b : ℕ} (hb : 0 < b) :
    halfNegBinMass b b = centralMass b / 2 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb.ne'
  unfold halfNegBinMass centralMass
  rw [centralBinom_succ_as_double]
  push_cast
  have hsub : (n + 1) + (n + 1) - 1 = 2 * n + 1 := by omega
  have hadd : (n + 1) + (n + 1) = 2 * (n + 1) := by omega
  rw [hsub, hadd,
    show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, pow_mul]
  norm_num
  ring

theorem halfNegBinMass_self_lower {b : ℕ} (hb : 0 < b) :
    1 / (4 * Real.sqrt (b : ℝ)) ≤ halfNegBinMass b b := by
  rw [halfNegBinMass_self hb]
  have h := centralMass_lower b hb
  calc
    _ = (1 / (2 * Real.sqrt (b : ℝ))) / 2 := by ring
    _ ≤ centralMass b / 2 := div_le_div_of_nonneg_right h (by norm_num)

theorem halfNegBinMass_self_upper {b : ℕ} (hb : 0 < b) :
    halfNegBinMass b b ≤ 1 / (2 * Real.sqrt ((b + 1 : ℕ) : ℝ)) := by
  rw [halfNegBinMass_self hb]
  have h := centralMass_upper b
  calc
    centralMass b / 2 ≤ (1 / Real.sqrt ((b + 1 : ℕ) : ℝ)) / 2 :=
      div_le_div_of_nonneg_right h (by norm_num)
    _ = 1 / (2 * Real.sqrt ((b + 1 : ℕ) : ℝ)) := by ring

theorem halfNegBinMass_adjacent_ratio (b j : ℕ) (hb : 0 < b) :
    halfNegBinMass b (j + 1) =
      (((b + j : ℕ) : ℝ) / (2 * ((j + 1 : ℕ) : ℝ))) * halfNegBinMass b j := by
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (by positivity : (2 * ((j + 1 : ℕ) : ℝ)) ≠ 0)).2
  simpa [div_mul_eq_mul_div, mul_assoc, mul_left_comm, mul_comm] using
    halfNegBinMass_adjacent b j hb

theorem halfNegBinMass_previous_ratio (b j : ℕ) (hb : 0 < b) :
    halfNegBinMass b j =
      ((2 * ((j + 1 : ℕ) : ℝ)) / ((b + j : ℕ) : ℝ)) *
        halfNegBinMass b (j + 1) := by
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (by positivity : (((b + j : ℕ) : ℝ)) ≠ 0)).2
  simpa [div_mul_eq_mul_div, mul_assoc, mul_left_comm, mul_comm] using
    (halfNegBinMass_adjacent b j hb).symm

/-- The elementary exponential inequality used to turn a product of nearby
mass ratios into a Gaussian-scale loss. -/
theorem exp_neg_two_mul_le_one_sub {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    Real.exp (-2 * x) ≤ 1 - x := by
  rw [show -2 * x = -(2 * x) by ring, Real.exp_neg]
  calc
    (Real.exp (2 * x))⁻¹ ≤ (1 + 2 * x)⁻¹ :=
      (inv_le_inv₀ (by positivity) (by positivity)).2 (by
        simpa [add_comm] using Real.add_one_le_exp (2 * x))
    _ ≤ 1 - x := by
      apply (inv_le_iff_one_le_mul₀ (by linarith)).2
      nlinarith

theorem exp_local_cost_le_pow {x : ℝ} (d : ℕ) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    Real.exp (-2 * x * d) ≤ (1 - x) ^ d := by
  have hpow := pow_le_pow_left₀ (Real.exp_nonneg (-2 * x))
    (exp_neg_two_mul_le_one_sub hx0 hx) d
  calc
    Real.exp (-2 * x * d) = Real.exp ((d : ℝ) * (-2 * x)) := by ring
    _ = Real.exp (-2 * x) ^ d := by rw [Real.exp_nat_mul]
    _ ≤ (1 - x) ^ d := hpow

theorem exp_neg_inv_mul_one_div_sqrt_le_centralMass {n : ℕ} (hn : 2 ≤ n) :
    Real.exp (-(1 / (n : ℝ))) /
        Real.sqrt (Real.pi * (n : ℝ)) ≤ centralMass n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hinv0 : (0 : ℝ) ≤ 1 / n := by positivity
  have hinvhalf : (1 / (n : ℝ)) ≤ 1 / 2 := by
    exact (div_le_div_iff₀ (by positivity) (by norm_num)).2 (by nlinarith)
  have hexp := exp_neg_two_mul_le_one_sub hinv0 hinvhalf
  have hexp2 :
      Real.exp (-(1 / (n : ℝ))) ^ 2 ≤ 1 - 1 / (n : ℝ) := by
    calc
      Real.exp (-(1 / (n : ℝ))) ^ 2 =
          Real.exp (-2 * (1 / (n : ℝ))) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      _ ≤ _ := hexp
  have hsqcore :
      (Real.exp (-(1 / (n : ℝ))) *
          Real.sqrt (Real.pi * ((n : ℝ) + 1 / 2))) ^ 2 ≤
        Real.sqrt (Real.pi * (n : ℝ)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity)]
    have hpi : 0 < Real.pi := Real.pi_pos
    have hrest :
        (1 - 1 / (n : ℝ)) * ((n : ℝ) + 1 / 2) ≤ n := by
      field_simp
      nlinarith
    calc
      Real.exp (-(1 / (n : ℝ))) ^ 2 *
          (Real.pi * ((n : ℝ) + 1 / 2)) ≤
        (1 - 1 / (n : ℝ)) * (Real.pi * ((n : ℝ) + 1 / 2)) :=
          mul_le_mul_of_nonneg_right hexp2 (by positivity)
      _ ≤ Real.pi * n := by
        nlinarith [mul_le_mul_of_nonneg_left hrest hpi.le]
  have hroot :
      Real.exp (-(1 / (n : ℝ))) *
          Real.sqrt (Real.pi * ((n : ℝ) + 1 / 2)) ≤
        Real.sqrt (Real.pi * (n : ℝ)) :=
    le_of_sq_le_sq hsqcore (by positivity)
  have hcompare :
      Real.exp (-(1 / (n : ℝ))) /
          Real.sqrt (Real.pi * (n : ℝ)) ≤
        1 / Real.sqrt (Real.pi * ((n : ℝ) + 1 / 2)) := by
    refine (div_le_div_iff₀ (Real.sqrt_pos.2 (by positivity))
      (Real.sqrt_pos.2 (by positivity))).2 ?_
    simpa [mul_comm] using hroot
  exact hcompare.trans (one_div_sqrt_pi_mul_add_half_le_centralMass n)

theorem halfNegBinMass_self_sharp_lower {b : ℕ} (hb : 2 ≤ b) :
    Real.exp (-(1 / (b : ℝ))) /
        (2 * Real.sqrt (Real.pi * (b : ℝ))) ≤ halfNegBinMass b b := by
  rw [halfNegBinMass_self (by omega)]
  have h := exp_neg_inv_mul_one_div_sqrt_le_centralMass hb
  calc
    _ = (Real.exp (-(1 / (b : ℝ))) /
        Real.sqrt (Real.pi * (b : ℝ))) / 2 := by ring
    _ ≤ centralMass b / 2 := div_le_div_of_nonneg_right h (by norm_num)

/-- A second-order lower exponential bound for `1 - x`. -/
theorem exp_neg_add_two_sq_le_one_sub {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    Real.exp (-(x + 2 * x ^ 2)) ≤ 1 - x := by
  rw [Real.exp_neg]
  have hy0 : 0 ≤ x + 2 * x ^ 2 := by positivity
  calc
    (Real.exp (x + 2 * x ^ 2))⁻¹ ≤ (1 + (x + 2 * x ^ 2))⁻¹ :=
      (inv_le_inv₀ (Real.exp_pos _) (by positivity)).2 (by
        simpa [add_comm] using Real.add_one_le_exp (x + 2 * x ^ 2))
    _ ≤ 1 - x := by
      apply (inv_le_iff_one_le_mul₀ (by positivity)).2
      have hpoly : 0 ≤ x ^ 2 * (1 - 2 * x) :=
        mul_nonneg (sq_nonneg x) (by linarith)
      nlinarith

/-- Sharp off-center exponent.  The leading term is `d² / (4b)`; all
remaining terms are of the local-limit error orders `d / b` and `d³ / b²`. -/
noncomputable def sharpOffCenterCost (b d : ℕ) : ℝ :=
  (d : ℝ) ^ 2 / (4 * (b : ℝ)) + 3 * d / (b : ℝ) +
    4 * (d : ℝ) ^ 3 / (b : ℝ) ^ 2

noncomputable def rightRatioLoss (b r : ℕ) : ℝ :=
  let x := ((r : ℝ) + 2) / (2 * ((b : ℝ) + r + 1))
  x + 2 * x ^ 2

noncomputable def leftRatioLoss (b r : ℕ) : ℝ :=
  let x := (r : ℝ) / (2 * (b : ℝ) - r - 1)
  x + 2 * x ^ 2

noncomputable def rightLossSum (b d : ℕ) : ℝ :=
  ∑ r ∈ Finset.range d, rightRatioLoss b r

noncomputable def leftLossSum (b d : ℕ) : ℝ :=
  ∑ r ∈ Finset.range d, leftRatioLoss b r

theorem rightRatioLoss_nonneg (b r : ℕ) : 0 ≤ rightRatioLoss b r := by
  unfold rightRatioLoss
  positivity

theorem rightRatioLoss_le_cost_diff {b r : ℕ} (hb : 0 < b) :
    rightRatioLoss b r ≤
      sharpOffCenterCost b (r + 1) - sharpOffCenterCost b r := by
  let x : ℝ := ((r : ℝ) + 2) / (2 * ((b : ℝ) + r + 1))
  let u : ℝ := ((r : ℝ) + 2) / (2 * (b : ℝ))
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hxu : x ≤ u := by
    dsimp [x, u]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have hnum : (0 : ℝ) ≤ r + 2 := by positivity
    nlinarith [mul_nonneg hnum (show (0 : ℝ) ≤ r + 1 by positivity)]
  have hsq : x ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ hx0 hxu 2
  have hfirst : rightRatioLoss b r ≤ u + 2 * u ^ 2 := by
    dsimp [rightRatioLoss, x] at ⊢
    nlinarith
  calc
    rightRatioLoss b r ≤ u + 2 * u ^ 2 := hfirst
    _ ≤ sharpOffCenterCost b (r + 1) - sharpOffCenterCost b r := by
      dsimp [u, sharpOffCenterCost]
      push_cast
      field_simp
      ring_nf
      nlinarith [show (0 : ℝ) ≤ r by positivity, show (0 : ℝ) ≤ b by positivity]

theorem rightLossSum_le_sharpOffCenterCost {b d : ℕ} (hb : 0 < b) :
    rightLossSum b d ≤ sharpOffCenterCost b d := by
  induction d with
  | zero => simp [rightLossSum, sharpOffCenterCost]
  | succ d ih =>
      rw [rightLossSum, Finset.sum_range_succ]
      unfold rightLossSum at ih
      linarith [rightRatioLoss_le_cost_diff (b := b) (r := d) hb]

theorem halfNegBinMass_right_adjacent_loss {b r : ℕ} (hb : 0 < b) :
    halfNegBinMass b (b + (r + 1)) =
      (1 - ((r : ℝ) + 2) / (2 * ((b : ℝ) + r + 1))) *
        halfNegBinMass b (b + r) := by
  rw [show b + (r + 1) = (b + r) + 1 by omega,
    halfNegBinMass_adjacent_ratio b (b + r) hb]
  congr 1
  push_cast
  field_simp
  ring

theorem exp_neg_rightRatioLoss_le_factor {b r : ℕ} (hb : 0 < b) :
    Real.exp (-rightRatioLoss b r) ≤
      1 - ((r : ℝ) + 2) / (2 * ((b : ℝ) + r + 1)) := by
  let x : ℝ := ((r : ℝ) + 2) / (2 * ((b : ℝ) + r + 1))
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hxhalf : x ≤ 1 / 2 := by
    dsimp [x]
    apply (div_le_iff₀ (by positivity)).2
    have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
    nlinarith
  simpa [rightRatioLoss, x] using exp_neg_add_two_sq_le_one_sub hx0 hxhalf

theorem exp_neg_rightLossSum_mul_self_le {b d : ℕ} (hb : 0 < b) :
    Real.exp (-rightLossSum b d) * halfNegBinMass b b ≤
      halfNegBinMass b (b + d) := by
  induction d with
  | zero => simp [rightLossSum]
  | succ d ih =>
      have hfactor0 :
          0 ≤ 1 - ((d : ℝ) + 2) / (2 * ((b : ℝ) + d + 1)) := by
        have h := exp_neg_rightRatioLoss_le_factor (b := b) (r := d) hb
        exact (Real.exp_pos _).le.trans h
      rw [rightLossSum, Finset.sum_range_succ]
      unfold rightLossSum at ih
      calc
        Real.exp (-(∑ r ∈ Finset.range d, rightRatioLoss b r +
              rightRatioLoss b d)) * halfNegBinMass b b =
            Real.exp (-rightRatioLoss b d) *
              (Real.exp (-rightLossSum b d) * halfNegBinMass b b) := by
          rw [show -(∑ r ∈ Finset.range d, rightRatioLoss b r +
              rightRatioLoss b d) =
                -rightRatioLoss b d + -rightLossSum b d by
              simp only [rightLossSum]; ring,
            Real.exp_add]
          ring
        _ ≤ (1 - ((d : ℝ) + 2) / (2 * ((b : ℝ) + d + 1))) *
              (Real.exp (-rightLossSum b d) * halfNegBinMass b b) :=
          mul_le_mul_of_nonneg_right
            (exp_neg_rightRatioLoss_le_factor (b := b) (r := d) hb)
            (mul_nonneg (Real.exp_pos _).le (halfNegBinMass_nonneg _ _))
        _ ≤ (1 - ((d : ℝ) + 2) / (2 * ((b : ℝ) + d + 1))) *
              halfNegBinMass b (b + d) :=
          mul_le_mul_of_nonneg_left ih hfactor0
        _ = halfNegBinMass b (b + (d + 1)) :=
          (halfNegBinMass_right_adjacent_loss (b := b) (r := d) hb).symm

theorem exp_neg_sharpOffCenterCost_mul_self_le_right {b d : ℕ} (hb : 0 < b) :
    Real.exp (-sharpOffCenterCost b d) * halfNegBinMass b b ≤
      halfNegBinMass b (b + d) := by
  calc
    _ ≤ Real.exp (-rightLossSum b d) * halfNegBinMass b b := by
      apply mul_le_mul_of_nonneg_right _ (halfNegBinMass_nonneg _ _)
      exact Real.exp_le_exp.mpr (neg_le_neg (rightLossSum_le_sharpOffCenterCost hb))
    _ ≤ _ := exp_neg_rightLossSum_mul_self_le hb

theorem halfNegBinMass_right_sharp_lower {b d : ℕ} (hb : 2 ≤ b) :
    Real.exp (-(sharpOffCenterCost b d + 1 / (b : ℝ))) /
          (2 * Real.sqrt (Real.pi * (b : ℝ))) ≤
      halfNegBinMass b (b + d) := by
  calc
    _ = Real.exp (-sharpOffCenterCost b d) *
          (Real.exp (-(1 / (b : ℝ))) /
            (2 * Real.sqrt (Real.pi * (b : ℝ)))) := by
      rw [show -(sharpOffCenterCost b d + 1 / (b : ℝ)) =
          -sharpOffCenterCost b d + -(1 / (b : ℝ)) by ring,
        Real.exp_add]
      ring
    _ ≤ Real.exp (-sharpOffCenterCost b d) * halfNegBinMass b b :=
      mul_le_mul_of_nonneg_left (halfNegBinMass_self_sharp_lower hb)
        (Real.exp_pos _).le
    _ ≤ _ := exp_neg_sharpOffCenterCost_mul_self_le_right (by omega)

theorem leftRatioLoss_le_cost_diff {b r : ℕ} (hrb : 4 * (r + 1) ≤ b) :
    leftRatioLoss b r ≤
      sharpOffCenterCost b (r + 1) - sharpOffCenterCost b r := by
  let x : ℝ := (r : ℝ) / (2 * (b : ℝ) - r - 1)
  let u : ℝ := (r : ℝ) / (2 * (b : ℝ)) +
    (r : ℝ) * (r + 1) / (2 * (b : ℝ) ^ 2)
  have hbpos : 0 < b := by omega
  have hrs : r + 1 ≤ b := by omega
  have hden : (0 : ℝ) < 2 * b - r - 1 := by
    have hrsR : ((r + 1 : ℕ) : ℝ) ≤ b := by exact_mod_cast hrs
    push_cast at hrsR
    nlinarith
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hxu : x ≤ u := by
    have hprod :
        0 ≤ (r : ℝ) * (r + 1) * ((b : ℝ) - r - 1) := by
      have hrsR : ((r + 1 : ℕ) : ℝ) ≤ b := by exact_mod_cast hrs
      push_cast at hrsR
      have : (0 : ℝ) ≤ (b : ℝ) - r - 1 := by linarith
      positivity
    dsimp [x, u]
    field_simp
    nlinarith
  have hur : u ≤ (r : ℝ) / b := by
    have hrsR : ((r + 1 : ℕ) : ℝ) ≤ b := by exact_mod_cast hrs
    push_cast at hrsR
    have hmul := mul_le_mul_of_nonneg_left hrsR
      (show (0 : ℝ) ≤ r by positivity)
    dsimp [u]
    field_simp
    nlinarith
  have hxr : x ≤ (r : ℝ) / b := hxu.trans hur
  have hsq : x ^ 2 ≤ ((r : ℝ) / b) ^ 2 := pow_le_pow_left₀ hx0 hxr 2
  have hfirst :
      leftRatioLoss b r ≤ u + 2 * ((r : ℝ) / b) ^ 2 := by
    dsimp [leftRatioLoss, x] at ⊢
    nlinarith
  calc
    leftRatioLoss b r ≤ u + 2 * ((r : ℝ) / b) ^ 2 := hfirst
    _ ≤ sharpOffCenterCost b (r + 1) - sharpOffCenterCost b r := by
      dsimp [u, sharpOffCenterCost]
      push_cast
      field_simp
      ring_nf
      nlinarith [show (0 : ℝ) ≤ r by positivity, show (0 : ℝ) ≤ b by positivity]

theorem leftLossSum_le_sharpOffCenterCost {b d : ℕ} (hd : 4 * d ≤ b) :
    leftLossSum b d ≤ sharpOffCenterCost b d := by
  have aux : ∀ e : ℕ, 4 * e ≤ b →
      leftLossSum b e ≤ sharpOffCenterCost b e := by
    intro e
    induction e with
    | zero => simp [leftLossSum, sharpOffCenterCost]
    | succ e ih =>
        intro he
        rw [leftLossSum, Finset.sum_range_succ]
        unfold leftLossSum at ih
        linarith [ih (by omega),
          leftRatioLoss_le_cost_diff (b := b) (r := e) he]
  exact aux d hd

theorem exp_neg_leftRatioLoss_le_factor {b r : ℕ} (hrb : 4 * (r + 1) ≤ b) :
    Real.exp (-leftRatioLoss b r) ≤
      1 - (r : ℝ) / (2 * (b : ℝ) - r - 1) := by
  let x : ℝ := (r : ℝ) / (2 * (b : ℝ) - r - 1)
  have hrs : r + 1 ≤ b := by omega
  have hden : (0 : ℝ) < 2 * b - r - 1 := by
    have hrsR : ((r + 1 : ℕ) : ℝ) ≤ b := by exact_mod_cast hrs
    push_cast at hrsR
    nlinarith
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hxhalf : x ≤ 1 / 2 := by
    dsimp [x]
    apply (div_le_iff₀ hden).2
    have hrbR : ((4 * (r + 1) : ℕ) : ℝ) ≤ b := by exact_mod_cast hrb
    push_cast at hrbR
    nlinarith
  simpa [leftRatioLoss, x] using exp_neg_add_two_sq_le_one_sub hx0 hxhalf

theorem halfNegBinMass_left_adjacent_ratio {b r : ℕ} (hb : 0 < b)
    (hr : r + 1 ≤ b) :
    halfNegBinMass b (b - (r + 1)) =
      (2 * ((b : ℝ) - r) / (2 * (b : ℝ) - r - 1)) *
        halfNegBinMass b (b - r) := by
  have hprev := halfNegBinMass_previous_ratio b (b - (r + 1)) hb
  rw [show b - (r + 1) + 1 = b - r by omega] at hprev
  rw [hprev]
  congr 1
  rw [show b + (b - (r + 1)) = 2 * b - r - 1 by omega,
    Nat.cast_sub (show 1 ≤ 2 * b - r by omega),
    Nat.cast_sub (show r ≤ 2 * b by omega)]
  push_cast
  rw [Nat.cast_sub (show r ≤ b by omega)]

theorem left_factor_mul_le_adjacent {b r : ℕ} (hrb : 4 * (r + 1) ≤ b) :
    (1 - (r : ℝ) / (2 * (b : ℝ) - r - 1)) *
        halfNegBinMass b (b - r) ≤
      halfNegBinMass b (b - (r + 1)) := by
  have hbpos : 0 < b := by omega
  have hrs : r + 1 ≤ b := by omega
  have hden : (0 : ℝ) < 2 * b - r - 1 := by
    have hrsR : ((r + 1 : ℕ) : ℝ) ≤ b := by exact_mod_cast hrs
    push_cast at hrsR
    nlinarith
  rw [halfNegBinMass_left_adjacent_ratio hbpos hrs]
  apply mul_le_mul_of_nonneg_right _ (halfNegBinMass_nonneg _ _)
  apply (le_div_iff₀ hden).2
  field_simp
  ring_nf
  linarith

theorem exp_neg_leftLossSum_mul_self_le {b d : ℕ} (hd : 4 * d ≤ b) :
    Real.exp (-leftLossSum b d) * halfNegBinMass b b ≤
      halfNegBinMass b (b - d) := by
  have aux : ∀ e : ℕ, 4 * e ≤ b →
      Real.exp (-leftLossSum b e) * halfNegBinMass b b ≤
        halfNegBinMass b (b - e) := by
    intro e
    induction e with
    | zero => simp [leftLossSum]
    | succ e ih =>
        intro he
        have hfactor0 :
            0 ≤ 1 - (e : ℝ) / (2 * (b : ℝ) - e - 1) := by
          have h := exp_neg_leftRatioLoss_le_factor (b := b) (r := e) he
          exact (Real.exp_pos _).le.trans h
        rw [leftLossSum, Finset.sum_range_succ]
        unfold leftLossSum at ih
        calc
          Real.exp (-(∑ r ∈ Finset.range e, leftRatioLoss b r +
                leftRatioLoss b e)) * halfNegBinMass b b =
              Real.exp (-leftRatioLoss b e) *
                (Real.exp (-leftLossSum b e) * halfNegBinMass b b) := by
            rw [show -(∑ r ∈ Finset.range e, leftRatioLoss b r +
                leftRatioLoss b e) =
                  -leftRatioLoss b e + -leftLossSum b e by
                simp only [leftLossSum]; ring,
              Real.exp_add]
            ring
          _ ≤ (1 - (e : ℝ) / (2 * (b : ℝ) - e - 1)) *
                (Real.exp (-leftLossSum b e) * halfNegBinMass b b) :=
            mul_le_mul_of_nonneg_right
              (exp_neg_leftRatioLoss_le_factor (b := b) (r := e) he)
              (mul_nonneg (Real.exp_pos _).le (halfNegBinMass_nonneg _ _))
          _ ≤ (1 - (e : ℝ) / (2 * (b : ℝ) - e - 1)) *
                halfNegBinMass b (b - e) :=
            mul_le_mul_of_nonneg_left (ih (by omega)) hfactor0
          _ ≤ halfNegBinMass b (b - (e + 1)) :=
            left_factor_mul_le_adjacent he
  exact aux d hd

theorem exp_neg_sharpOffCenterCost_mul_self_le_left {b d : ℕ}
    (hd : 4 * d ≤ b) :
    Real.exp (-sharpOffCenterCost b d) * halfNegBinMass b b ≤
      halfNegBinMass b (b - d) := by
  calc
    _ ≤ Real.exp (-leftLossSum b d) * halfNegBinMass b b := by
      apply mul_le_mul_of_nonneg_right _ (halfNegBinMass_nonneg _ _)
      exact Real.exp_le_exp.mpr (neg_le_neg (leftLossSum_le_sharpOffCenterCost hd))
    _ ≤ _ := exp_neg_leftLossSum_mul_self_le hd

theorem halfNegBinMass_left_sharp_lower {b d : ℕ} (hb : 2 ≤ b)
    (hd : 4 * d ≤ b) :
    Real.exp (-(sharpOffCenterCost b d + 1 / (b : ℝ))) /
          (2 * Real.sqrt (Real.pi * (b : ℝ))) ≤
      halfNegBinMass b (b - d) := by
  calc
    _ = Real.exp (-sharpOffCenterCost b d) *
          (Real.exp (-(1 / (b : ℝ))) /
            (2 * Real.sqrt (Real.pi * (b : ℝ)))) := by
      rw [show -(sharpOffCenterCost b d + 1 / (b : ℝ)) =
          -sharpOffCenterCost b d + -(1 / (b : ℝ)) by ring,
        Real.exp_add]
      ring
    _ ≤ Real.exp (-sharpOffCenterCost b d) * halfNegBinMass b b :=
      mul_le_mul_of_nonneg_left (halfNegBinMass_self_sharp_lower hb)
        (Real.exp_pos _).le
    _ ≤ _ := exp_neg_sharpOffCenterCost_mul_self_le_left hd

/-- The complete sharp local exponent, including the explicit central Wallis
normalization loss. -/
noncomputable def sharpLocalCost (b b' : ℕ) : ℝ :=
  sharpOffCenterCost b (Nat.dist b b') + 1 / (b : ℝ)

/-- A two-sided local lower bound with the sharp Gaussian coefficient `1 / 4`.
The remainder is explicit:
`3 d / b + 4 d^3 / b^2 + 1 / b`, where `d = Nat.dist b b'`. -/
theorem halfNegBinMass_sharp_local_lower {b b' : ℕ} (hb : 2 ≤ b)
    (hd : 4 * Nat.dist b b' ≤ b) :
    Real.exp (-sharpLocalCost b b') /
          (2 * Real.sqrt (Real.pi * (b : ℝ))) ≤
      halfNegBinMass b b' := by
  rcases le_total b b' with hle | hle
  · have hdist : Nat.dist b b' = b' - b := Nat.dist_eq_sub_of_le hle
    have heq : b + Nat.dist b b' = b' := by rw [hdist]; omega
    simpa only [sharpLocalCost, heq] using
      (halfNegBinMass_right_sharp_lower (b := b) (d := Nat.dist b b') hb)
  · have hdist : Nat.dist b b' = b - b' := Nat.dist_eq_sub_of_le_right hle
    have heq : b - Nat.dist b b' = b' := by rw [hdist]; omega
    simpa only [sharpLocalCost, heq] using
      (halfNegBinMass_left_sharp_lower (b := b) (d := Nat.dist b b') hb hd)

/-- A uniform lower bound for every adjacent ratio in a quarter-width window. -/
noncomputable def localFactor (b d : ℕ) : ℝ :=
  1 - ((d + 2 : ℕ) : ℝ) / (b : ℝ)

theorem localParameter_nonneg {b d : ℕ} (hb : 8 ≤ b) (hd : 4 * d ≤ b) :
    0 ≤ ((d + 2 : ℕ) : ℝ) / (b : ℝ) := by positivity

theorem localParameter_le_half {b d : ℕ} (hb : 8 ≤ b) (hd : 4 * d ≤ b) :
    ((d + 2 : ℕ) : ℝ) / (b : ℝ) ≤ 1 / 2 := by
  have hlin : 2 * (d + 2) ≤ b := by omega
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < b)).2
  have hlinR : ((2 * (d + 2) : ℕ) : ℝ) ≤ (b : ℝ) := by exact_mod_cast hlin
  push_cast at hlinR
  norm_num at hlinR ⊢
  linarith

theorem localFactor_nonneg {b d : ℕ} (hb : 8 ≤ b) (hd : 4 * d ≤ b) :
    0 ≤ localFactor b d := by
  unfold localFactor
  linarith [localParameter_le_half hb hd]

theorem localFactor_mul_right_le {b d r : ℕ} (hb : 8 ≤ b) (hd : 4 * d ≤ b)
    (hr : r ≤ d) :
    localFactor b d * halfNegBinMass b (b + r) ≤
      halfNegBinMass b (b + (r + 1)) := by
  have hbpos : 0 < b := by omega
  have hbR : (0 : ℝ) < b := by positivity
  have hrR : (r : ℝ) ≤ d := by exact_mod_cast hr
  have hfrac :
      ((r : ℝ) + 2) / (2 * ((b : ℝ) + r + 1)) ≤
        ((d : ℝ) + 2) / (b : ℝ) := by
    apply (div_le_div_iff₀ (by positivity) hbR).2
    have hmul : 0 ≤ ((d : ℝ) - r) * b :=
      mul_nonneg (sub_nonneg.2 hrR) hbR.le
    nlinarith
  have hcoef :
      localFactor b d ≤
        (((b + (b + r) : ℕ) : ℝ) / (2 * (((b + r) + 1 : ℕ) : ℝ))) := by
    unfold localFactor
    push_cast
    calc
      1 - ((d : ℝ) + 2) / b ≤
          1 - ((r : ℝ) + 2) / (2 * ((b : ℝ) + r + 1)) :=
        sub_le_sub_left hfrac 1
      _ = (b + (b + r)) / (2 * ((b + r) + 1)) := by
        field_simp
        ring
  rw [show b + (r + 1) = (b + r) + 1 by omega,
    halfNegBinMass_adjacent_ratio b (b + r) hbpos]
  exact mul_le_mul_of_nonneg_right hcoef (halfNegBinMass_nonneg _ _)

theorem localFactor_pow_mul_self_le_right {b d : ℕ} (hb : 8 ≤ b) (hd : 4 * d ≤ b) :
    localFactor b d ^ d * halfNegBinMass b b ≤ halfNegBinMass b (b + d) := by
  have hc : 0 ≤ localFactor b d := localFactor_nonneg hb hd
  have aux : ∀ r : ℕ, r ≤ d →
      localFactor b d ^ r * halfNegBinMass b b ≤ halfNegBinMass b (b + r) := by
    intro r hr
    induction r with
    | zero => simp
    | succ r ih =>
        have hr' : r ≤ d := by omega
        calc
          localFactor b d ^ (r + 1) * halfNegBinMass b b =
              localFactor b d *
                (localFactor b d ^ r * halfNegBinMass b b) := by
            rw [pow_succ']
            ring
          _ ≤ localFactor b d * halfNegBinMass b (b + r) :=
            mul_le_mul_of_nonneg_left (ih hr') hc
          _ ≤ halfNegBinMass b (b + (r + 1)) :=
            localFactor_mul_right_le hb hd hr'
  exact aux d le_rfl

/-- Explicit lower local bound on the upper side of the center.  Its exponent
has precisely the quadratic-over-linear scale required in Proposition A.7. -/
theorem halfNegBinMass_right_lower {b d : ℕ} (hb : 8 ≤ b) (hd : 4 * d ≤ b) :
    Real.exp
          (-2 * (((d + 2 : ℕ) : ℝ) / (b : ℝ)) * d) *
        (1 / (4 * Real.sqrt (b : ℝ))) ≤
      halfNegBinMass b (b + d) := by
  have hp := exp_local_cost_le_pow (x := ((d + 2 : ℕ) : ℝ) / (b : ℝ)) d
    (localParameter_nonneg hb hd) (localParameter_le_half hb hd)
  have hc := halfNegBinMass_self_lower (show 0 < b by omega)
  calc
    _ ≤ localFactor b d ^ d * (1 / (4 * Real.sqrt (b : ℝ))) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ ≤ localFactor b d ^ d * halfNegBinMass b b :=
      mul_le_mul_of_nonneg_left hc (pow_nonneg (localFactor_nonneg hb hd) _)
    _ ≤ halfNegBinMass b (b + d) := localFactor_pow_mul_self_le_right hb hd

theorem halfNegBinMass_right_le_self {b d : ℕ} (hb : 0 < b) :
    halfNegBinMass b (b + d) ≤ halfNegBinMass b b := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [show b + (d + 1) = (b + d) + 1 by omega,
        halfNegBinMass_adjacent_ratio b (b + d) hb]
      refine (mul_le_of_le_one_left (halfNegBinMass_nonneg _ _) ?_).trans ih
      apply (div_le_one (by positivity : (0 : ℝ) < 2 * (((b + d) + 1 : ℕ) : ℝ))).2
      push_cast
      linarith

theorem halfNegBinMass_right_upper {b d : ℕ} (hb : 0 < b) :
    halfNegBinMass b (b + d) ≤
      1 / (2 * Real.sqrt ((b + 1 : ℕ) : ℝ)) :=
  (halfNegBinMass_right_le_self hb).trans (halfNegBinMass_self_upper hb)

theorem localFactor_mul_left_le {b d r : ℕ} (hb : 8 ≤ b) (hd : 4 * d ≤ b)
    (hr : r ≤ d) :
    localFactor b d * halfNegBinMass b (b - r) ≤
      halfNegBinMass b (b - (r + 1)) := by
  have hbpos : 0 < b := by omega
  have hrb : r + 1 ≤ b := by omega
  have hrR : (r : ℝ) ≤ d := by exact_mod_cast hr
  have hrbR : (r : ℝ) ≤ b := by
    exact_mod_cast (show r ≤ b by omega)
  have hbR : (0 : ℝ) < b := by positivity
  have hdenR : (0 : ℝ) < 2 * b - r - 1 := by
    have : (r : ℝ) + 1 ≤ b := by exact_mod_cast hrb
    linarith
  have hbase :
      1 - (r : ℝ) / b ≤ 2 * (b - r) / (2 * b - r - 1) := by
    have heq : 1 - (r : ℝ) / b = (b - r) / b := by
      field_simp
    rw [heq]
    apply (div_le_div_iff₀ hbR hdenR).2
    have hprod : 0 ≤ ((b : ℝ) - r) * (r + 1) :=
      mul_nonneg (sub_nonneg.2 hrbR) (by positivity)
    nlinarith
  have hfirst : localFactor b d ≤ 1 - (r : ℝ) / b := by
    unfold localFactor
    push_cast
    have hdiv : (r : ℝ) / b ≤ ((d : ℝ) + 2) / b :=
      div_le_div_of_nonneg_right (by linarith) hbR.le
    linarith
  have hcoef :
      localFactor b d ≤
        (2 : ℝ) * ((b - (r + 1) + 1 : ℕ) : ℝ) /
          ((b + (b - (r + 1)) : ℕ) : ℝ) := by
    calc
      localFactor b d ≤ 1 - (r : ℝ) / b := hfirst
      _ ≤ 2 * (b - r) / (2 * b - r - 1) := hbase
      _ = (2 : ℝ) * ((b - (r + 1) + 1 : ℕ) : ℝ) /
          ((b + (b - (r + 1)) : ℕ) : ℝ) := by
        rw [show b - (r + 1) + 1 = b - r by omega,
          show b + (b - (r + 1)) = 2 * b - r - 1 by omega]
        rw [Nat.cast_sub (show r ≤ b by omega),
          Nat.cast_sub (show 1 ≤ 2 * b - r by omega),
          Nat.cast_sub (show r ≤ 2 * b by omega)]
        push_cast
        rfl
  have hprev :
      halfNegBinMass b (b - (r + 1)) =
        ((2 : ℝ) * ((b - (r + 1) + 1 : ℕ) : ℝ) /
          ((b + (b - (r + 1)) : ℕ) : ℝ)) * halfNegBinMass b (b - r) := by
    simpa only [show b - (r + 1) + 1 = b - r by omega] using
      halfNegBinMass_previous_ratio b (b - (r + 1)) hbpos
  rw [hprev]
  exact mul_le_mul_of_nonneg_right hcoef (halfNegBinMass_nonneg _ _)

theorem localFactor_pow_mul_self_le_left {b d : ℕ} (hb : 8 ≤ b) (hd : 4 * d ≤ b) :
    localFactor b d ^ d * halfNegBinMass b b ≤ halfNegBinMass b (b - d) := by
  have hc : 0 ≤ localFactor b d := localFactor_nonneg hb hd
  have aux : ∀ r : ℕ, r ≤ d →
      localFactor b d ^ r * halfNegBinMass b b ≤ halfNegBinMass b (b - r) := by
    intro r hr
    induction r with
    | zero => simp
    | succ r ih =>
        have hr' : r ≤ d := by omega
        calc
          localFactor b d ^ (r + 1) * halfNegBinMass b b =
              localFactor b d *
                (localFactor b d ^ r * halfNegBinMass b b) := by
            rw [pow_succ']
            ring
          _ ≤ localFactor b d * halfNegBinMass b (b - r) :=
            mul_le_mul_of_nonneg_left (ih hr') hc
          _ ≤ halfNegBinMass b (b - (r + 1)) :=
            localFactor_mul_left_le hb hd hr'
  exact aux d le_rfl

theorem halfNegBinMass_left_lower {b d : ℕ} (hb : 8 ≤ b) (hd : 4 * d ≤ b) :
    Real.exp
          (-2 * (((d + 2 : ℕ) : ℝ) / (b : ℝ)) * d) *
        (1 / (4 * Real.sqrt (b : ℝ))) ≤
      halfNegBinMass b (b - d) := by
  have hp := exp_local_cost_le_pow (x := ((d + 2 : ℕ) : ℝ) / (b : ℝ)) d
    (localParameter_nonneg hb hd) (localParameter_le_half hb hd)
  have hc := halfNegBinMass_self_lower (show 0 < b by omega)
  calc
    _ ≤ localFactor b d ^ d * (1 / (4 * Real.sqrt (b : ℝ))) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ ≤ localFactor b d ^ d * halfNegBinMass b b :=
      mul_le_mul_of_nonneg_left hc (pow_nonneg (localFactor_nonneg hb hd) _)
    _ ≤ halfNegBinMass b (b - d) := localFactor_pow_mul_self_le_left hb hd

theorem halfNegBinMass_left_le_two_self {b d : ℕ} (hb : 0 < b) (hd : d ≤ b) :
    halfNegBinMass b (b - d) ≤ 2 * halfNegBinMass b b := by
  induction d with
  | zero =>
      simp only [Nat.sub_zero]
      nlinarith [halfNegBinMass_nonneg b b]
  | succ d ih =>
      have hd' : d ≤ b := by omega
      have hdB : d + 1 ≤ b := by omega
      by_cases hd0 : d = 0
      · subst d
        have hprev := halfNegBinMass_previous_ratio b (b - 1) hb
        rw [show b - 1 + 1 = b by omega] at hprev
        rw [hprev]
        refine mul_le_mul_of_nonneg_right ?_ (halfNegBinMass_nonneg _ _)
        have hden : (0 : ℝ) < ((b + (b - 1) : ℕ) : ℝ) := by positivity
        apply (div_le_iff₀ hden).2
        push_cast
        rw [Nat.cast_sub (show 1 ≤ b by omega)]
        have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
        norm_num at *
        nlinarith
      · calc
          halfNegBinMass b (b - (d + 1)) =
              ((2 : ℝ) * ((b - (d + 1) + 1 : ℕ) : ℝ) /
                ((b + (b - (d + 1)) : ℕ) : ℝ)) *
                halfNegBinMass b (b - d) := by
            simpa only [show b - (d + 1) + 1 = b - d by omega] using
              halfNegBinMass_previous_ratio b (b - (d + 1)) hb
          _ ≤ halfNegBinMass b (b - d) := by
            apply mul_le_of_le_one_left (halfNegBinMass_nonneg _ _)
            have hden : (0 : ℝ) < ((b + (b - (d + 1)) : ℕ) : ℝ) := by positivity
            apply (div_le_one hden).2
            rw [show b - (d + 1) + 1 = b - d by omega,
              show b + (b - (d + 1)) = 2 * b - d - 1 by omega]
            rw [Nat.cast_sub hd', Nat.cast_sub (show 1 ≤ 2 * b - d by omega),
              Nat.cast_sub (show d ≤ 2 * b by omega)]
            push_cast
            have hdR : (1 : ℝ) ≤ d := by
              exact_mod_cast (Nat.one_le_iff_ne_zero.2 hd0)
            nlinarith
          _ ≤ 2 * halfNegBinMass b b := ih hd'

theorem halfNegBinMass_left_upper {b d : ℕ} (hb : 0 < b) (hd : d ≤ b) :
    halfNegBinMass b (b - d) ≤
      1 / Real.sqrt ((b + 1 : ℕ) : ℝ) := by
  calc
    _ ≤ 2 * halfNegBinMass b b := halfNegBinMass_left_le_two_self hb hd
    _ ≤ 2 * (1 / (2 * Real.sqrt ((b + 1 : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_left (halfNegBinMass_self_upper hb) (by norm_num)
    _ = 1 / Real.sqrt ((b + 1 : ℕ) : ℝ) := by ring

/-- A two-sided local bound stated directly using the unsigned displacement
`Nat.dist b b'`.  The lower bound has the local-CLT scale
`b⁻¹ᐟ² exp (-O(dist b b' ^ 2 / b))`; the upper bound has the matching
`b⁻¹ᐟ²` order. -/
theorem halfNegBinMass_local_bounds {b b' : ℕ} (hb : 8 ≤ b)
    (hd : 4 * Nat.dist b b' ≤ b) :
    Real.exp
          (-2 * (((Nat.dist b b' + 2 : ℕ) : ℝ) / (b : ℝ)) * Nat.dist b b') *
          (1 / (4 * Real.sqrt (b : ℝ))) ≤ halfNegBinMass b b' ∧
      halfNegBinMass b b' ≤ 1 / Real.sqrt ((b + 1 : ℕ) : ℝ) := by
  have hbpos : 0 < b := by omega
  rcases le_total b b' with hle | hle
  · have hdist : Nat.dist b b' = b' - b := Nat.dist_eq_sub_of_le hle
    have heq : b + Nat.dist b b' = b' := by rw [hdist]; omega
    constructor
    · simpa only [heq] using halfNegBinMass_right_lower hb hd
    ·
      have h := halfNegBinMass_right_upper (d := Nat.dist b b') hbpos
      have hsmall : 0 ≤ 1 / (2 * Real.sqrt ((b + 1 : ℕ) : ℝ)) := by positivity
      calc
        halfNegBinMass b b' = halfNegBinMass b (b + Nat.dist b b') := by rw [heq]
        _ ≤ 1 / (2 * Real.sqrt ((b + 1 : ℕ) : ℝ)) := h
        _ ≤ 2 * (1 / (2 * Real.sqrt ((b + 1 : ℕ) : ℝ))) := by nlinarith
        _ = 1 / Real.sqrt ((b + 1 : ℕ) : ℝ) := by ring
  · have hdist : Nat.dist b b' = b - b' := Nat.dist_eq_sub_of_le_right hle
    have heq : b - Nat.dist b b' = b' := by rw [hdist]; omega
    constructor
    · simpa only [heq] using halfNegBinMass_left_lower hb hd
    · calc
        halfNegBinMass b b' = halfNegBinMass b (b - Nat.dist b b') := by rw [heq]
        _ ≤ 1 / Real.sqrt ((b + 1 : ℕ) : ℝ) :=
          halfNegBinMass_left_upper hbpos (by rw [hdist]; omega)

/-- The pointwise local estimate multiplies without further loss.  This is the
form used when bounding the probability of an entire Appendix-A trajectory. -/
theorem prod_halfNegBinMass_local_lower {ι : Type*} (s : Finset ι)
    (b b' : ι → ℕ) (hb : ∀ i ∈ s, 8 ≤ b i)
    (hd : ∀ i ∈ s, 4 * Nat.dist (b i) (b' i) ≤ b i) :
    ∏ i ∈ s,
        (Real.exp
            (-2 * (((Nat.dist (b i) (b' i) + 2 : ℕ) : ℝ) / (b i : ℝ)) *
              Nat.dist (b i) (b' i)) *
          (1 / (4 * Real.sqrt (b i : ℝ)))) ≤
      ∏ i ∈ s, halfNegBinMass (b i) (b' i) := by
  gcongr with i hi
  exact (halfNegBinMass_local_bounds (hb i hi) (hd i hi)).1

/-- Product form of the sharp local estimate.  The exponent has leading
coefficient `1 / 4` transition by transition, with only the displayed
explicit remainders in `sharpLocalCost`. -/
theorem prod_halfNegBinMass_sharp_local_lower {ι : Type*} (s : Finset ι)
    (b b' : ι → ℕ) (hb : ∀ i ∈ s, 2 ≤ b i)
    (hd : ∀ i ∈ s, 4 * Nat.dist (b i) (b' i) ≤ b i) :
    ∏ i ∈ s,
        (Real.exp (-sharpLocalCost (b i) (b' i)) /
          (2 * Real.sqrt (Real.pi * (b i : ℝ)))) ≤
      ∏ i ∈ s, halfNegBinMass (b i) (b' i) := by
  gcongr with i hi
  exact halfNegBinMass_sharp_local_lower (hb i hi) (hd i hi)

end Erdos1166.HLOZAppendixA
