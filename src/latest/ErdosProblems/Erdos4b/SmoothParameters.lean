/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SmoothRankin

/-!
# A discrete Rankin-scale parameter ray

Working on a sparse, explicitly dyadic parameter ray removes every rounding
issue from the smooth-number estimate.  The sparseness is harmless: the final
theorem only asks for witnesses arbitrarily far out.

For a fixed loss parameter `a` and a ray parameter `r`, put

* `V = 2^(2^r)`,
* `T = 2^r V`,
* `K = 2^(a+2r) V`,
* `S = rT`,
* `X = 2^K`, `Y = 2^S`, and `U = XVr`.

Thus `log Y / log₂ X` has the required Rankin order, while the Rankin
exponent `delta = 1/T` satisfies the exact identities
`Y^delta = 2^r` and `delta * log X = 2^(a+r) log 2`.
-/

open Filter Real Asymptotics
open scoped BigOperators Asymptotics

namespace Erdos4b
namespace SmoothParameters

noncomputable section

/-- The rapidly growing common dyadic factor. -/
def core (r : Nat) : Nat := 2 ^ (2 ^ r)

/-- Reciprocal of the Rankin exponent. -/
def rankinDenominator (r : Nat) : Nat := 2 ^ r * core r

/-- Binary logarithm of the primary sieve frontier. -/
def primaryExponent (a r : Nat) : Nat := 2 ^ (a + 2 * r) * core r

/-- Binary logarithm of the smoothness frontier. -/
def smoothExponent (r : Nat) : Nat := r * rankinDenominator r

/-- Primary sieve frontier. -/
def primaryFrontier (a r : Nat) : Nat := 2 ^ primaryExponent a r

/-- Smoothness frontier. -/
def smoothFrontier (r : Nat) : Nat := 2 ^ smoothExponent r

/-- Length of the interval to be covered. -/
def intervalLength (a r : Nat) : Nat :=
  primaryFrontier a r * core r * r

/-- Rankin exponent. -/
noncomputable def delta (r : Nat) : Real :=
  (rankinDenominator r : Real)⁻¹

theorem core_pos (r : Nat) : 0 < core r := by
  simp [core]

theorem rankinDenominator_pos (r : Nat) : 0 < rankinDenominator r := by
  simp [rankinDenominator, core]

theorem rankinDenominator_two_le (r : Nat) :
    2 ≤ rankinDenominator r := by
  rw [rankinDenominator]
  have hcore : 2 ≤ core r := by
    rw [core]
    have h : 1 < (2 : Nat) ^ (2 ^ r) :=
      one_lt_pow₀ (by norm_num) (by positivity)
    omega
  have hpow : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  nlinarith

theorem primaryExponent_pos (a r : Nat) : 0 < primaryExponent a r := by
  simp [primaryExponent, core]

theorem primaryFrontier_pos (a r : Nat) : 0 < primaryFrontier a r := by
  simp [primaryFrontier]

theorem smoothFrontier_pos (r : Nat) : 0 < smoothFrontier r := by
  simp [smoothFrontier]

theorem intervalLength_pos {a r : Nat} (hr : 0 < r) :
    0 < intervalLength a r := by
  exact Nat.mul_pos (Nat.mul_pos (primaryFrontier_pos a r) (core_pos r)) hr

theorem delta_pos (r : Nat) : 0 < delta r := by
  exact inv_pos.mpr (by exact_mod_cast rankinDenominator_pos r)

theorem delta_le_half (r : Nat) : delta r ≤ 1 / 2 := by
  have hT : (2 : Real) ≤ rankinDenominator r := by
    exact_mod_cast rankinDenominator_two_le r
  have hTpos : (0 : Real) < rankinDenominator r := by
    exact_mod_cast rankinDenominator_pos r
  simpa [delta, one_div] using
    ((inv_le_inv₀ hTpos (by norm_num : (0 : Real) < 2)).2 hT)

theorem delta_inv (r : Nat) :
    (delta r)⁻¹ = (rankinDenominator r : Real) := by
  rw [delta, inv_inv]

theorem rankinSplitPoint_delta (r : Nat) :
    SmoothRankin.rankinSplitPoint (delta r) = rankinDenominator r := by
  rw [SmoothRankin.rankinSplitPoint, delta_inv]
  exact Nat.ceil_natCast _

@[simp]
theorem log_two_smoothFrontier (r : Nat) :
    Nat.log 2 (smoothFrontier r) = smoothExponent r := by
  exact Nat.log_pow (by norm_num) _

theorem primaryExponent_div_rankinDenominator (a r : Nat) :
    (primaryExponent a r : Real) / rankinDenominator r =
      (2 : Real) ^ (a + r) := by
  have hcoreR : (core r : Real) ≠ 0 := by
    exact_mod_cast (core_pos r).ne'
  have hpowR : ((2 : Real) ^ r) ≠ 0 := by positivity
  rw [primaryExponent, rankinDenominator]
  push_cast
  rw [show a + 2 * r = (a + r) + r by omega, pow_add]
  field_simp

theorem delta_mul_log_primaryFrontier (a r : Nat) :
    delta r * Real.log (primaryFrontier a r : Real) =
      (2 : Real) ^ (a + r) * Real.log 2 := by
  rw [primaryFrontier, Nat.cast_pow, Real.log_pow]
  rw [delta, inv_eq_one_div]
  calc
    1 / (rankinDenominator r : Real) *
          ((primaryExponent a r : Real) * Real.log 2) =
        ((primaryExponent a r : Real) / rankinDenominator r) *
          Real.log 2 := by ring
    _ = (2 : Real) ^ (a + r) * Real.log 2 := by
      rw [primaryExponent_div_rankinDenominator]

theorem delta_mul_smoothExponent (r : Nat) :
    delta r * (smoothExponent r : Real) = r := by
  have hT : (rankinDenominator r : Real) ≠ 0 := by
    exact_mod_cast (rankinDenominator_pos r).ne'
  rw [delta, smoothExponent]
  push_cast
  field_simp

theorem rankinTail_eq (r : Nat) :
    (((2 : Real) ^ delta r) ^
        (Nat.log 2 (smoothFrontier r) + 2)) =
      (2 : Real) ^ ((r : Real) + 2 * delta r) := by
  rw [log_two_smoothFrontier]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : (0 : Real) ≤ 2)]
  congr 1
  push_cast
  rw [mul_add, delta_mul_smoothExponent]
  ring

theorem two_mul_delta_le_one (r : Nat) : 2 * delta r ≤ 1 := by
  have h := delta_le_half r
  linarith

theorem rankinTail_le (r : Nat) :
    (((2 : Real) ^ delta r) ^
        (Nat.log 2 (smoothFrontier r) + 2)) ≤
      2 * (2 : Real) ^ r := by
  rw [rankinTail_eq]
  calc
    (2 : Real) ^ ((r : Real) + 2 * delta r) ≤
        (2 : Real) ^ ((r : Real) + 1) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (by linarith [two_mul_delta_le_one r])
    _ = 2 * (2 : Real) ^ r := by
      rw [Real.rpow_add (by norm_num : (0 : Real) < 2),
        Real.rpow_one, Real.rpow_natCast]
      ring

theorem log_rankinDenominator (r : Nat) :
    Real.log (rankinDenominator r : Real) =
      ((r : Real) + (2 : Real) ^ r) * Real.log 2 := by
  rw [rankinDenominator, core]
  push_cast
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_pow]
  push_cast
  ring

theorem harmonic_rankinDenominator_le (r : Nat) :
    (harmonic (rankinDenominator r) : Real) ≤
      1 + ((r : Real) + (2 : Real) ^ r) * Real.log 2 := by
  exact (harmonic_le_one_add_log (rankinDenominator r)).trans_eq
    (congrArg (fun z : Real => 1 + z) (log_rankinDenominator r))

/-- A closed constant for the weighted-harmonic bracket on the dyadic ray. -/
noncomputable def dyadicBracketConstant : Real :=
  4 + 8 * Real.log 2 + 2 / Real.log 2

theorem dyadicBracketConstant_pos : 0 < dyadicBracketConstant := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  dsimp [dyadicBracketConstant]
  positivity

theorem dyadicBracket_le {r : Nat} (_hr : 1 ≤ r) :
    4 * (harmonic (SmoothRankin.rankinSplitPoint (delta r)) : Real) +
        (((2 : Real) ^ delta r) ^
          (Nat.log 2 (smoothFrontier r) + 2)) / Real.log 2 ≤
      dyadicBracketConstant * (2 : Real) ^ r := by
  have hrpow : (r : Real) ≤ (2 : Real) ^ r := by
    exact_mod_cast Nat.le_of_lt r.lt_two_pow_self
  have honepow : (1 : Real) ≤ (2 : Real) ^ r := by
    exact one_le_pow₀ (by norm_num : (1 : Real) ≤ 2)
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  rw [rankinSplitPoint_delta]
  calc
    4 * (harmonic (rankinDenominator r) : Real) +
          (((2 : Real) ^ delta r) ^
            (Nat.log 2 (smoothFrontier r) + 2)) / Real.log 2 ≤
        4 * (1 + ((r : Real) + (2 : Real) ^ r) * Real.log 2) +
          (2 * (2 : Real) ^ r) / Real.log 2 := by
      gcongr
      · exact harmonic_rankinDenominator_le r
      · exact rankinTail_le r
    _ ≤ (4 + 8 * Real.log 2 + 2 / Real.log 2) *
          (2 : Real) ^ r := by
      have hlog_nonneg : 0 ≤ Real.log (2 : Real) := hlog2.le
      calc
        4 * (1 + ((r : Real) + (2 : Real) ^ r) * Real.log 2) +
              (2 * (2 : Real) ^ r) / Real.log 2 ≤
            4 * ((2 : Real) ^ r +
              (2 * (2 : Real) ^ r) * Real.log 2) +
              (2 * (2 : Real) ^ r) / Real.log 2 := by
          gcongr
          nlinarith
        _ = (4 + 8 * Real.log 2 + 2 / Real.log 2) *
              (2 : Real) ^ r := by ring
    _ = dyadicBracketConstant * (2 : Real) ^ r := rfl

/-- The fixed coefficient multiplying `2^r` in the Euler exponent after a
uniform Chebyshev constant has been selected. -/
noncomputable def eulerExponentConstant (C : Real) : Real :=
  Erdos469.rankinEulerConstant *
    (2 * C / Real.log 2) * dyadicBracketConstant

theorem eulerExponentConstant_pos {C : Real} (hC : 0 < C) :
    0 < eulerExponentConstant C := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  exact mul_pos
    (mul_pos Erdos469.rankinEulerConstant_pos
      (div_pos (mul_pos (by norm_num) hC) hlog2))
    dyadicBracketConstant_pos

/-- Uniform exponential bound for the finite Rankin Euler product on the
discrete parameter ray. -/
theorem exists_eulerExponentConstant :
    ∃ B : Real, 0 < B ∧ ∀ r : Nat, 1 ≤ r →
      Erdos469.smoothRankinEulerProduct (delta r) (smoothFrontier r) ≤
        Real.exp (B * (2 : Real) ^ r) := by
  obtain ⟨C, hC, hcheb⟩ :=
    Erdos387.PrimeReciprocal.exists_uniform_primeCounting_le_div_log_all
  refine ⟨eulerExponentConstant C, eulerExponentConstant_pos hC, ?_⟩
  intro r hr
  have hEuler := SmoothRankin.smoothRankinEulerProduct_le_exp_dyadic_canonical
    hC (delta_pos r) (delta_le_half r) hcheb (smoothFrontier r)
  apply hEuler.trans
  apply Real.exp_le_exp.mpr
  have hbracket := dyadicBracket_le hr
  calc
    Erdos469.rankinEulerConstant *
        ((2 * C / Real.log 2) *
          (4 * (harmonic (SmoothRankin.rankinSplitPoint (delta r)) : Real) +
            ((2 : Real) ^ delta r) ^
                (Nat.log 2 (smoothFrontier r) + 2) / Real.log 2)) ≤
      Erdos469.rankinEulerConstant *
        ((2 * C / Real.log 2) *
          (dyadicBracketConstant * (2 : Real) ^ r)) := by
      apply mul_le_mul_of_nonneg_left
      · apply mul_le_mul_of_nonneg_left hbracket
        positivity
      · exact Erdos469.rankinEulerConstant_pos.le
    _ = eulerExponentConstant C * (2 : Real) ^ r := by
      rw [eulerExponentConstant]
      ring

/-- Corresponding Rankin bound for the actual smooth residual exception. -/
theorem exists_card_smoothResidualException_dyadic_bound :
    ∃ B : Real, 0 < B ∧ ∀ (a r : Nat), 1 ≤ r →
      ((smoothResidualException (intervalLength a r)
          (smoothFrontier r)).card : Real) ≤
        (intervalLength a r : Real) ^ (1 - delta r) *
          Real.exp (B * (2 : Real) ^ r) := by
  obtain ⟨C, hC, hcheb⟩ :=
    Erdos387.PrimeReciprocal.exists_uniform_primeCounting_le_div_log_all
  refine ⟨eulerExponentConstant C, eulerExponentConstant_pos hC, ?_⟩
  intro a r hr
  have hU : 0 < intervalLength a r := intervalLength_pos (by omega)
  have hRankin := card_smoothResidualException_rankin_le
    (U := intervalLength a r) (y := smoothFrontier r)
    (δ := delta r) hU (delta_pos r)
    ((delta_le_half r).trans_lt (by norm_num))
  apply hRankin.trans
  apply mul_le_mul_of_nonneg_left _
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hEuler := SmoothRankin.smoothRankinEulerProduct_le_exp_dyadic_canonical
    hC (delta_pos r) (delta_le_half r) hcheb (smoothFrontier r)
  apply hEuler.trans
  apply Real.exp_le_exp.mpr
  have hbracket := dyadicBracket_le hr
  calc
    Erdos469.rankinEulerConstant *
        ((2 * C / Real.log 2) *
          (4 * (harmonic (SmoothRankin.rankinSplitPoint (delta r)) : Real) +
            ((2 : Real) ^ delta r) ^
                (Nat.log 2 (smoothFrontier r) + 2) / Real.log 2)) ≤
      Erdos469.rankinEulerConstant *
        ((2 * C / Real.log 2) *
          (dyadicBracketConstant * (2 : Real) ^ r)) := by
      apply mul_le_mul_of_nonneg_left
      · apply mul_le_mul_of_nonneg_left hbracket
        positivity
      · exact Erdos469.rankinEulerConstant_pos.le
    _ = eulerExponentConstant C * (2 : Real) ^ r := by
      rw [eulerExponentConstant]
      ring

/-! ## Absorbing the smooth exception into the fresh-prime budget -/

theorem self_le_core (r : Nat) : r ≤ core r := by
  have hr : r ≤ 2 ^ r := Nat.le_of_lt r.lt_two_pow_self
  have hpow : 2 ^ r ≤ 2 ^ (2 ^ r) :=
    pow_le_pow_right₀ (by norm_num : (1 : Nat) ≤ 2) hr
  exact hr.trans (by simpa [core] using hpow)

theorem intervalLength_le_primary_mul_core_sq (a r : Nat) :
    intervalLength a r ≤ primaryFrontier a r * core r ^ 2 := by
  rw [intervalLength, pow_two]
  simpa [mul_assoc] using
    (Nat.mul_le_mul_left (primaryFrontier a r)
      (Nat.mul_le_mul_left (core r) (self_le_core r)))

theorem primaryExponent_le_core_sq_of
    {a r : Nat} (har : a + 2 * r ≤ 2 ^ r) :
    primaryExponent a r ≤ core r ^ 2 := by
  rw [primaryExponent, core, pow_two]
  exact Nat.mul_le_mul_right (2 ^ (2 ^ r))
    (pow_le_pow_right₀ (by norm_num : (1 : Nat) ≤ 2) har)

theorem log_core (r : Nat) :
    Real.log (core r : Real) = (2 : Real) ^ r * Real.log 2 := by
  rw [core, Nat.cast_pow, Real.log_pow]
  push_cast
  rfl

theorem exp_neg_four_log_two_mul_two_pow (r : Nat) :
    Real.exp (-4 * Real.log 2 * (2 : Real) ^ r) =
      (((core r : Real) ^ 4)⁻¹) := by
  have hcorepos : (0 : Real) < core r := by
    exact_mod_cast core_pos r
  have hlog := log_core r
  rw [show -4 * Real.log 2 * (2 : Real) ^ r =
      -(4 * Real.log (core r : Real)) by rw [hlog]; ring]
  rw [Real.exp_neg]
  congr 1
  rw [← Real.rpow_natCast]
  rw [Real.rpow_def_of_pos hcorepos]
  congr 1
  ring

theorem rpow_one_sub_eq_mul_exp_neg {U : Nat} (hU : 0 < U)
    (d : Real) :
    (U : Real) ^ (1 - d) =
      (U : Real) * Real.exp (-d * Real.log (U : Real)) := by
  have hUR : (0 : Real) < U := by exact_mod_cast hU
  rw [Real.rpow_def_of_pos hUR]
  rw [show Real.log (U : Real) * (1 - d) =
      Real.log (U : Real) + (-d * Real.log (U : Real)) by ring]
  rw [Real.exp_add, Real.exp_log hUR]

theorem primaryFrontier_le_intervalLength {a r : Nat} (hr : 1 ≤ r) :
    primaryFrontier a r ≤ intervalLength a r := by
  rw [intervalLength]
  have hfactor : 1 ≤ core r * r :=
    Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero (core_pos r).ne' (by omega))
  simpa [mul_assoc] using Nat.mul_le_mul_left (primaryFrontier a r) hfactor

theorem delta_mul_log_intervalLength_lower {a r : Nat} (hr : 1 ≤ r) :
    (2 : Real) ^ (a + r) * Real.log 2 ≤
      delta r * Real.log (intervalLength a r : Real) := by
  have hXpos : (0 : Real) < primaryFrontier a r := by
    exact_mod_cast primaryFrontier_pos a r
  have hlog : Real.log (primaryFrontier a r : Real) ≤
      Real.log (intervalLength a r : Real) := by
    exact Real.log_le_log hXpos
      (by exact_mod_cast primaryFrontier_le_intervalLength (a := a) hr)
  rw [← delta_mul_log_primaryFrontier a r]
  exact mul_le_mul_of_nonneg_left hlog (delta_pos r).le

/-- If `a` dominates the fixed Euler constant and the elementary exponent
comparison has entered its stable range, the smooth exception fits inside
the canonical `X / K` fresh-prime budget. -/
theorem card_smoothResidualException_le_primary_div
    {B : Real} {a r : Nat} (hr : 1 ≤ r)
    (hB : B + 4 * Real.log 2 ≤ (2 : Real) ^ a * Real.log 2)
    (har : a + 2 * r ≤ 2 ^ r)
    (hcard :
      ((smoothResidualException (intervalLength a r)
          (smoothFrontier r)).card : Real) ≤
        (intervalLength a r : Real) ^ (1 - delta r) *
          Real.exp (B * (2 : Real) ^ r)) :
    ((smoothResidualException (intervalLength a r)
        (smoothFrontier r)).card : Real) ≤
      (primaryFrontier a r : Real) / primaryExponent a r := by
  let U := intervalLength a r
  let X := primaryFrontier a r
  let V := core r
  let K := primaryExponent a r
  have hU : 0 < U := intervalLength_pos (by omega)
  have hX : 0 < X := primaryFrontier_pos a r
  have hV : 0 < V := core_pos r
  have hK : 0 < K := primaryExponent_pos a r
  have hsave := delta_mul_log_intervalLength_lower (a := a) hr
  have hpowadd : (2 : Real) ^ (a + r) =
      (2 : Real) ^ a * (2 : Real) ^ r := by rw [pow_add]
  have hexponent :
      -delta r * Real.log (U : Real) + B * (2 : Real) ^ r ≤
        -4 * Real.log 2 * (2 : Real) ^ r := by
    dsimp only [U] at hsave ⊢
    rw [hpowadd] at hsave
    have hB' := mul_le_mul_of_nonneg_right hB
      (show 0 ≤ (2 : Real) ^ r by positivity)
    nlinarith
  have hanalytic :
      (U : Real) ^ (1 - delta r) *
          Real.exp (B * (2 : Real) ^ r) ≤
        (U : Real) * (((V : Real) ^ 4)⁻¹) := by
    rw [rpow_one_sub_eq_mul_exp_neg hU]
    rw [mul_assoc]
    rw [← Real.exp_add]
    apply mul_le_mul_of_nonneg_left
    · calc
        Real.exp (-delta r * Real.log (U : Real) +
            B * (2 : Real) ^ r) ≤
            Real.exp (-4 * Real.log 2 * (2 : Real) ^ r) :=
          Real.exp_le_exp.mpr hexponent
        _ = (((V : Real) ^ 4)⁻¹) := by
          simpa only [V] using exp_neg_four_log_two_mul_two_pow r
    · positivity
  have hUupper : (U : Real) ≤ (X : Real) * (V : Real) ^ 2 := by
    exact_mod_cast intervalLength_le_primary_mul_core_sq a r
  have hKupper : (K : Real) ≤ (V : Real) ^ 2 := by
    exact_mod_cast primaryExponent_le_core_sq_of har
  apply hcard.trans
  apply hanalytic.trans
  have hVR : (0 : Real) < V := by exact_mod_cast hV
  have hKR : (0 : Real) < K := by exact_mod_cast hK
  calc
    (U : Real) * (((V : Real) ^ 4)⁻¹) ≤
        ((X : Real) * (V : Real) ^ 2) * (((V : Real) ^ 4)⁻¹) :=
      mul_le_mul_of_nonneg_right hUupper (by positivity)
    _ = (X : Real) / (V : Real) ^ 2 := by
      field_simp
    _ ≤ (X : Real) / K := by
      exact div_le_div_of_nonneg_left (by positivity) hKR hKupper
    _ = (primaryFrontier a r : Real) / primaryExponent a r := rfl

theorem three_mul_le_two_pow {r : Nat} (hr : 4 ≤ r) :
    3 * r ≤ 2 ^ r := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ r hr ih =>
      have hthree : 3 ≤ 2 ^ r := by
        have : 3 ≤ 3 * r := by omega
        exact this.trans ih
      calc
        3 * (r + 1) = 3 * r + 3 := by ring
        _ ≤ 2 ^ r + 2 ^ r := Nat.add_le_add ih hthree
        _ = 2 ^ (r + 1) := by rw [pow_succ]; ring

theorem stable_exponent_comparison {a r : Nat}
    (hra : a ≤ r) (hr4 : 4 ≤ r) :
    a + 2 * r ≤ 2 ^ r := by
  calc
    a + 2 * r ≤ 3 * r := by omega
    _ ≤ 2 ^ r := three_mul_le_two_pow hr4

theorem exists_lossExponent (B : Real) :
    ∃ a : Nat,
      B + 4 * Real.log 2 ≤ (2 : Real) ^ a * Real.log 2 := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hpow :=
    (tendsto_pow_atTop_atTop_of_one_lt
      (by norm_num : (1 : Real) < 2)).eventually_ge_atTop
      ((B + 4 * Real.log 2) / Real.log 2)
  obtain ⟨a, ha⟩ := hpow.exists
  refine ⟨a, ?_⟩
  exact (div_le_iff₀ hlog2).mp (by simpa [mul_comm] using ha)

/-- The smooth residual exception is eventually smaller than the natural
`X / log X`-scale fresh-prime budget on one fixed dyadic Rankin ray. -/
theorem exists_eventually_card_smoothResidualException_le_primary_div :
    ∃ a R : Nat, ∀ r : Nat, R ≤ r →
      ((smoothResidualException (intervalLength a r)
          (smoothFrontier r)).card : Real) ≤
        (primaryFrontier a r : Real) / primaryExponent a r := by
  obtain ⟨B, _hBpos, hcard⟩ :=
    exists_card_smoothResidualException_dyadic_bound
  obtain ⟨a, ha⟩ := exists_lossExponent B
  refine ⟨a, max a 4, ?_⟩
  intro r hr
  have hra : a ≤ r := (le_max_left a 4).trans hr
  have hr4 : 4 ≤ r := (le_max_right a 4).trans hr
  exact card_smoothResidualException_le_primary_div
    (show 1 ≤ r by omega) ha
    (stable_exponent_comparison hra hr4)
    (hcard a r (by omega))

end
end SmoothParameters
end Erdos4b
