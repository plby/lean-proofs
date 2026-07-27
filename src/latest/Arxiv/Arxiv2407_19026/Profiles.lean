import Arxiv.Arxiv2407_19026.Optimization

/-!
# The analytic profiles in Section 4

This file records the functions used in the four optimization rounds and
their exact diagonal values.  Decimal constants from the paper are written
as rationals, so the only transcendental quantities that remain are genuine
`Real.log` and `Real.exp` values.
-/

noncomputable section

namespace Arxiv2407_19026

/-- The entropy exponent corresponding to the Erdős--Szekeres bound. -/
def ramseyEntropy (z : ℝ) : ℝ :=
  (z + 1) * Real.log (z + 1) - z * Real.log z

/-- The correction term used in the optimization rounds. -/
def ramseyCorrection (β z : ℝ) : ℝ :=
  (-(1 / 4 : ℝ) * z + β * z ^ 2 + (2 / 25 : ℝ) * z ^ 3) *
    Real.exp (-z)

/-- The exponent denoted `F_i` in the proof of `t:main`. -/
def optimizedRamseyExponent (β z : ℝ) : ℝ :=
  ramseyEntropy z + ramseyCorrection β z

/-- The final exponent, corresponding to `β₃ = 0.03`. -/
def mainRamseyExponent : ℝ → ℝ :=
  optimizedRamseyExponent (3 / 100)

/-- The common book parameter `M(λ)=λe⁻ˡᵃᵐᵇᵈᵃ`. -/
def optimizationM (z : ℝ) : ℝ :=
  z * Real.exp (-z)

/-- The explicit derivative of `optimizedRamseyExponent`.

Writing it as a separate function avoids hiding numerical certification
behind the noncomputable `deriv` operator. -/
def optimizedRamseySlope (β z : ℝ) : ℝ :=
  Real.log (z + 1) - Real.log z +
    (-(1 / 4 : ℝ) + 2 * β * z + (6 / 25 : ℝ) * z ^ 2 -
      (-(1 / 4 : ℝ) * z + β * z ^ 2 + (2 / 25 : ℝ) * z ^ 3)) *
      Real.exp (-z)

/-- The red-density parameter prescribed by Theorem `t:general`.
The sign here is the corrected one: the profiles in the paper have positive,
not negative, slope. -/
def optimizationP (β z : ℝ) : ℝ :=
  1 - Real.exp (-optimizedRamseySlope β z)

/-- The first-coordinate book parameter prescribed by `t:general`. -/
def optimizationX (β z : ℝ) : ℝ :=
  optimizationP β z ^
      ((1 : ℝ) / (1 - optimizationM z)) *
    (1 - optimizationM z)

/-- The improvement parameter passed from one optimization round to the
next. -/
def nextAlpha (β : ℝ) : ℝ :=
  ((17 / 100 : ℝ) - β) * Real.exp (-1)

lemma hasDerivAt_ramseyEntropy {z : ℝ} (hz : 0 < z) :
    HasDerivAt ramseyEntropy
      (Real.log (z + 1) - Real.log z) z := by
  unfold ramseyEntropy
  convert (((hasDerivAt_id z).add_const 1).mul
      (((hasDerivAt_id z).add_const 1).log (by positivity))).sub
    ((hasDerivAt_id z).mul ((hasDerivAt_id z).log hz.ne')) using 1
  all_goals try rfl
  simp only [Function.id_def, one_mul]
  field_simp [hz.ne']
  ring

lemma hasDerivAt_ramseyCorrection (β : ℝ) {z : ℝ} :
    HasDerivAt (ramseyCorrection β)
      ((-(1 / 4 : ℝ) + 2 * β * z + (6 / 25 : ℝ) * z ^ 2 -
        (-(1 / 4 : ℝ) * z + β * z ^ 2 + (2 / 25 : ℝ) * z ^ 3)) *
        Real.exp (-z)) z := by
  unfold ramseyCorrection
  convert (((((hasDerivAt_const z (-(1 / 4 : ℝ))).mul
        (hasDerivAt_id z)).add
      ((hasDerivAt_const z β).mul ((hasDerivAt_id z).pow 2))).add
    ((hasDerivAt_const z (2 / 25 : ℝ)).mul
      ((hasDerivAt_id z).pow 3))).mul
    (hasDerivAt_id z).neg.exp) using 1
  all_goals try rfl
  simp only [Function.id_def, Pi.add_apply, Pi.mul_apply, Pi.pow_apply,
    Pi.neg_apply]
  norm_num
  ring

lemma hasDerivAt_optimizedRamseyExponent (β : ℝ)
    {z : ℝ} (hz : 0 < z) :
    HasDerivAt (optimizedRamseyExponent β)
      (optimizedRamseySlope β z) z := by
  unfold optimizedRamseyExponent optimizedRamseySlope
  convert (hasDerivAt_ramseyEntropy hz).add
      (hasDerivAt_ramseyCorrection β) using 1
  all_goals rfl

lemma ramseyEntropy_one :
    ramseyEntropy 1 = 2 * Real.log 2 := by
  simp [ramseyEntropy]
  ring_nf

lemma ramseyCorrection_one (β : ℝ) :
    ramseyCorrection β 1 =
      (β - 17 / 100) * Real.exp (-1) := by
  simp [ramseyCorrection]
  ring

lemma optimizedRamseyExponent_one (β : ℝ) :
    optimizedRamseyExponent β 1 =
      2 * Real.log 2 + (β - 17 / 100) * Real.exp (-1) := by
  rw [optimizedRamseyExponent, ramseyEntropy_one,
    ramseyCorrection_one]

lemma mainRamseyExponent_one :
    mainRamseyExponent 1 =
      2 * Real.log 2 - 7 / 50 * Real.exp (-1) := by
  rw [mainRamseyExponent, optimizedRamseyExponent_one]
  ring

lemma exp_mainRamseyExponent_one :
    Real.exp (mainRamseyExponent 1) =
      4 * Real.exp (-(7 / 50 * Real.exp (-1))) := by
  rw [mainRamseyExponent_one, Real.exp_sub]
  have htwo :
      Real.exp (2 * Real.log 2) = 4 := by
    rw [show (2 : ℝ) * Real.log 2 =
      (2 : ℕ) * Real.log 2 by norm_num, Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [htwo, Real.exp_neg (7 / 50 * Real.exp (-1))]
  rfl

/-- The final diagonal base is strictly below `3.8`. -/
lemma exp_mainRamseyExponent_one_lt_three_point_eight :
    Real.exp (mainRamseyExponent 1) < 19 / 5 := by
  rw [exp_mainRamseyExponent_one]
  let a : ℝ := 7 / 50 * Real.exp (-1)
  have ha : 0 < a := by positivity
  have hseries :
      1 + a + a ^ 2 / 2 ≤ Real.exp a := by
    have h := Real.sum_le_exp_of_nonneg ha.le 3
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    nlinarith
  have hlower : 20 / 19 < 1 + a + a ^ 2 / 2 := by
    dsimp [a]
    nlinarith [Real.exp_neg_one_gt_d9]
  have hexp : 20 / 19 < Real.exp a :=
    hlower.trans_le hseries
  rw [show -(7 / 50 * Real.exp (-1)) = -a by rfl,
    Real.exp_neg]
  have hinv : (Real.exp a)⁻¹ < (20 / 19 : ℝ)⁻¹ :=
    (inv_lt_inv₀ (Real.exp_pos a) (by norm_num)).2 hexp
  norm_num at hinv ⊢
  linarith

end Arxiv2407_19026
