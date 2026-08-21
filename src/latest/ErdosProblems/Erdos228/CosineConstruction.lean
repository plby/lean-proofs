import ErdosProblems.Erdos228.Bernstein
import ErdosProblems.Erdos228.CosineAlgebra
import ErdosProblems.Erdos228.EvenConstruction
import ErdosProblems.Erdos228.Interpolation
import ErdosProblems.Erdos228.Intervals
import ErdosProblems.Erdos228.OddSine
import ErdosProblems.Erdos228.RootCount

/-!
# The exceptional intervals for the Rudin--Shapiro cosine block

This file packages the finite-grid part of the cosine construction in
Balister--Bollobas--Morris--Sahasrabudhe--Tiba.  In particular, a *bad cell*
is a cell of the `pi / n` grid on which the Rudin--Shapiro cosine falls below
the required threshold, and the dangerous intervals are its maximal runs.

The definitions use closed cells.  This is convenient analytically and is
the reason that a chosen boundary contact can belong to two adjacent cells.
-/

namespace Erdos228.CosineConstruction

open Set
open scoped BigOperators

noncomputable section

/-- The numerator in BBMST's parameter equation
`gamma * n = 2^(t+11) + 2^t - 1`. -/
def parameterNumerator (t : ℕ) : ℕ := 2 ^ (t + 11) + 2 ^ t - 1

/-- The value of `gamma` forced by the integer parameters `n,t`. -/
def parameterGamma (n t : ℕ) : ℝ := parameterNumerator t / n

/-- The lower-bound constant `2^-8 gamma^(7/2)`, written without a real
power: for nonnegative `gamma`, `gamma^3 * sqrt gamma = gamma^(7/2)`. -/
def cosineDelta (gamma : ℝ) : ℝ :=
  (1 / 2 ^ 8 : ℝ) * gamma ^ 3 * Real.sqrt gamma

/-- The target lower threshold for the cosine coordinate. -/
def cosineThreshold (n : ℕ) (gamma : ℝ) : ℝ :=
  cosineDelta gamma * Real.sqrt n

/-- The arithmetic hypotheses on the parameters used in the cosine
construction.  They are kept together so downstream statements cannot
silently omit either the exact equation or the quantitative window. -/
structure Parameters (n t : ℕ) (gamma : ℝ) : Prop where
  n_pos : 0 < n
  t_odd : Odd t
  equation : gamma * n = parameterNumerator t
  gamma_lower : (1 / 2 ^ 43 : ℝ) < gamma
  gamma_upper : gamma ≤ (1 / 2 ^ 40 : ℝ)

theorem Parameters.gamma_pos {n t : ℕ} {gamma : ℝ}
    (h : Parameters n t gamma) : 0 < gamma := by
  exact lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / 2 ^ 43) h.gamma_lower.le

theorem cosineDelta_pos {gamma : ℝ} (hgamma : 0 < gamma) :
    0 < cosineDelta gamma := by
  simp only [cosineDelta]
  positivity

theorem cosineThreshold_pos {n : ℕ} {gamma : ℝ}
    (hn : 0 < n) (hgamma : 0 < gamma) : 0 < cosineThreshold n gamma := by
  simp only [cosineThreshold]
  exact mul_pos (cosineDelta_pos hgamma) (Real.sqrt_pos.2 (by exact_mod_cast hn))

theorem Parameters.toEvenParameters {n t : ℕ} {gamma : ℝ}
    (h : Parameters n t gamma) : EvenParameters n t gamma where
  t_odd := h.t_odd
  gamma_pos := h.gamma_pos
  gamma_le := h.gamma_upper
  equation := by simpa [parameterNumerator, evenGammaNumerator] using h.equation

theorem Parameters.scale {n t : ℕ} {gamma : ℝ}
    (h : Parameters n t gamma) : 2 ^ (t + 3) ≤ n := by
  exact (Nat.pow_le_pow_right (by norm_num) (by omega)).trans
    h.toEvenParameters.pow_t_add_eleven_le_n

theorem Parameters.eta_pos {n t : ℕ} {gamma : ℝ}
    (h : Parameters n t gamma) :
    0 < 2 * (evenT t : ℝ) * Real.pi / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast h.n_pos
  have hTR : (0 : ℝ) < evenT t := by
    exact_mod_cast (show 0 < evenT t by simp [evenT])
  exact div_pos (mul_pos (mul_pos (by norm_num) hTR) Real.pi_pos) hnR

theorem Parameters.eta_lt {n t : ℕ} {gamma : ℝ}
    (h : Parameters n t gamma) :
    2 * (evenT t : ℝ) * Real.pi / n < 1 / 2048 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast h.n_pos
  have hTle : (2 * evenT t : ℝ) ≤ gamma * n := by
    rw [h.equation]
    exact_mod_cast (show 2 * evenT t ≤ parameterNumerator t by
      rw [parameterNumerator, two_mul_evenT]
      have hp : 0 < 2 ^ t := by positivity
      omega)
  have hpi : Real.pi < 4 := Real.pi_lt_four
  have hgam : gamma ≤ 1 / 2 ^ 40 := h.gamma_upper
  have hgamma : 0 < gamma := h.gamma_pos
  calc
    2 * (evenT t : ℝ) * Real.pi / n ≤
        (gamma * n) * Real.pi / n := by
      gcongr
    _ = gamma * Real.pi := by field_simp
    _ < gamma * 4 := by gcongr
    _ ≤ (1 / 2 ^ 40 : ℝ) * 4 := by gcongr
    _ < 1 / 2048 := by norm_num

theorem Parameters.ratio_lower {n t : ℕ} {gamma : ℝ}
    (h : Parameters n t gamma) :
    (15 / 16 : ℝ) * (gamma * n) < 2 * evenT t := by
  rw [h.equation]
  have hnat : 15 * parameterNumerator t < 16 * (2 * evenT t) := by
    rw [parameterNumerator, evenT]
    have hp : 0 < 2 ^ t := by positivity
    rw [show 2 ^ (t + 11) = 2 ^ t * 2 ^ 11 by rw [pow_add],
      show 2 ^ (t + 10) = 2 ^ t * 2 ^ 10 by rw [pow_add]]
    norm_num
    omega
  have hreal : (15 : ℝ) * parameterNumerator t < 16 * (2 * evenT t) := by
    exact_mod_cast hnat
  norm_num at hreal ⊢
  nlinarith

private theorem sqrt_two_mul_evenT (t : ℕ) :
    Real.sqrt (2 * (evenT t : ℝ)) =
      32 * Real.sqrt (2 ^ (t + 1) : ℝ) := by
  have hpow : (2 * (evenT t : ℝ)) = (2 ^ (t + 1) : ℝ) * 32 ^ 2 := by
    norm_num [evenT, pow_add]
    ring
  rw [hpow, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 ^ (t + 1)),
    Real.sqrt_sq_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 32)]
  ring

/-- The normalized seven-cell lower bound rescales to the exact threshold
required by the final construction. -/
theorem Parameters.threshold_le_normalized_good {n t : ℕ} {gamma : ℝ}
    (h : Parameters n t gamma) :
    cosineThreshold n gamma ≤
      Real.sqrt (2 ^ (t + 1) : ℝ) *
        (2 * (evenT t : ℝ) * Real.pi / n) ^ 3 / 128 := by
  let A : ℝ := gamma * n
  let B : ℝ := 2 * evenT t
  have hnR : (0 : ℝ) < n := by exact_mod_cast h.n_pos
  have hgamma : 0 < gamma := h.gamma_pos
  have hA : 0 < A := mul_pos hgamma hnR
  have hB : 0 < B := by
    dsimp [B]
    have hT : (0 : ℝ) < evenT t := by
      exact_mod_cast (show 0 < evenT t by simp [evenT])
    positivity
  have hratio : (15 / 16 : ℝ) * A < B := by
    simpa [A, B] using h.ratio_lower
  have hratioSq : (15 / 16 : ℝ) ^ 2 * A < B := by
    have : (15 / 16 : ℝ) ^ 2 < 15 / 16 := by norm_num
    nlinarith
  have hsqrtRatio : (15 / 16 : ℝ) * Real.sqrt A < Real.sqrt B := by
    have hsA : 0 ≤ Real.sqrt A := Real.sqrt_nonneg _
    have hsB : 0 ≤ Real.sqrt B := Real.sqrt_nonneg _
    have hsA2 : (Real.sqrt A) ^ 2 = A := Real.sq_sqrt hA.le
    have hsB2 : (Real.sqrt B) ^ 2 = B := Real.sq_sqrt hB.le
    nlinarith
  have hcubes : (15 / 16 : ℝ) ^ 3 * A ^ 3 < B ^ 3 := by
    have hp := pow_lt_pow_left₀ hratio
      (mul_nonneg (by norm_num) hA.le) (by norm_num : (3 : ℕ) ≠ 0)
    simpa only [mul_pow] using hp
  have hprod : (15 / 16 : ℝ) ^ 4 * (A ^ 3 * Real.sqrt A) <
      B ^ 3 * Real.sqrt B := by
    have hsApos : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
    have hrpos : (0 : ℝ) < 15 / 16 := by norm_num
    have hm := mul_lt_mul hcubes hsqrtRatio.le
      (mul_pos hrpos hsApos) (pow_nonneg hB.le 3)
    calc
      (15 / 16 : ℝ) ^ 4 * (A ^ 3 * Real.sqrt A) =
          ((15 / 16 : ℝ) ^ 3 * A ^ 3) *
            ((15 / 16 : ℝ) * Real.sqrt A) := by ring
      _ < B ^ 3 * Real.sqrt B := hm
  have hnumeric : (16 : ℝ) < 3 ^ 3 * (15 / 16 : ℝ) ^ 4 := by norm_num
  have hpiCube : (3 : ℝ) ^ 3 < Real.pi ^ 3 := by
    nlinarith [Real.pi_gt_three, sq_nonneg (Real.pi - 3)]
  have hmain : 16 * (A ^ 3 * Real.sqrt A) <
      Real.pi ^ 3 * (B ^ 3 * Real.sqrt B) := by
    have hAprodpos : 0 < A ^ 3 * Real.sqrt A :=
      mul_pos (pow_pos hA 3) (Real.sqrt_pos.2 hA)
    have hrprodpos : 0 < (15 / 16 : ℝ) ^ 4 * (A ^ 3 * Real.sqrt A) := by
      positivity
    have hpiCubePos : 0 < Real.pi ^ 3 := pow_pos Real.pi_pos 3
    calc
      16 * (A ^ 3 * Real.sqrt A) <
          (3 ^ 3 * (15 / 16 : ℝ) ^ 4) * (A ^ 3 * Real.sqrt A) := by
        exact mul_lt_mul_of_pos_right hnumeric hAprodpos
      _ = 3 ^ 3 * ((15 / 16 : ℝ) ^ 4 * (A ^ 3 * Real.sqrt A)) := by ring
      _ < Real.pi ^ 3 * ((15 / 16 : ℝ) ^ 4 * (A ^ 3 * Real.sqrt A)) :=
        mul_lt_mul_of_pos_right hpiCube hrprodpos
      _ < Real.pi ^ 3 * (B ^ 3 * Real.sqrt B) :=
        mul_lt_mul_of_pos_left hprod hpiCubePos
  have hsqrtA : Real.sqrt A = Real.sqrt gamma * Real.sqrt n := by
    dsimp [A]
    rw [Real.sqrt_mul (le_of_lt hgamma)]
  have hsqrtB : Real.sqrt B = 32 * Real.sqrt (2 ^ (t + 1) : ℝ) := by
    simpa [B] using sqrt_two_mul_evenT t
  have hscaled :
      (1 / 256 : ℝ) * gamma ^ 3 * Real.sqrt gamma * Real.sqrt n <
        Real.sqrt (2 ^ (t + 1) : ℝ) *
          (B * Real.pi / n) ^ 3 / 128 := by
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
    have hlhs :
        (1 / 256 : ℝ) * gamma ^ 3 * Real.sqrt gamma * Real.sqrt n =
          (16 * (A ^ 3 * Real.sqrt A)) / (4096 * n ^ 3) := by
      calc
        (1 / 256 : ℝ) * gamma ^ 3 * Real.sqrt gamma * Real.sqrt n =
            (1 / 256 : ℝ) * gamma ^ 3 *
              (Real.sqrt gamma * Real.sqrt n) := by ring
        _ = (1 / 256 : ℝ) * gamma ^ 3 * Real.sqrt A := by rw [← hsqrtA]
        _ = (16 * (A ^ 3 * Real.sqrt A)) / (4096 * n ^ 3) := by
          dsimp [A]
          field_simp [hn0]
          ring
    have hs : Real.sqrt (2 ^ (t + 1) : ℝ) = Real.sqrt B / 32 := by
      rw [hsqrtB]
      ring
    have hrhs :
        Real.sqrt (2 ^ (t + 1) : ℝ) * (B * Real.pi / n) ^ 3 / 128 =
          (Real.pi ^ 3 * (B ^ 3 * Real.sqrt B)) / (4096 * n ^ 3) := by
      rw [hs]
      field_simp [hn0]
      ring
    rw [hlhs, hrhs]
    exact div_lt_div_of_pos_right hmain (by positivity)
  norm_num [cosineThreshold, cosineDelta, B] at hscaled ⊢
  exact hscaled.le

/-! ## The normalized Rudin--Shapiro modes -/

/-- Normalizing factor for the Rudin--Shapiro energy identity. -/
def rsNormalization (t : ℕ) : ℝ := (Real.sqrt (2 ^ (t + 1) : ℝ))⁻¹

/-- The normalized `r`th formal derivative of `P_t(exp(i x/T))`.
The factor `(i/T)^r` includes the chain rule. -/
def normalizedPDerivative (r t : ℕ) (x : ℝ) : ℂ :=
  (rsNormalization t : ℂ) *
    (Complex.I / (evenT t : ℝ)) ^ r *
      ((Erdos228.Bernstein.eulerDerivative^[r]) (rudinShapiroP t)).eval
        (unitPoint (x / evenT t))

/-- The companion normalized formal derivative. -/
def normalizedQDerivative (r t : ℕ) (x : ℝ) : ℂ :=
  (rsNormalization t : ℂ) *
    (Complex.I / (evenT t : ℝ)) ^ r *
      ((Erdos228.Bernstein.eulerDerivative^[r]) (rudinShapiroQ t)).eval
        (unitPoint (x / evenT t))

/-- BBMST's normalized two-mode function. -/
def normalizedH (t : ℕ) (x : ℝ) : ℂ :=
  unitPoint x * normalizedPDerivative 0 t x +
    unitPoint (2 * x) * normalizedQDerivative 0 t x

theorem rsNormalization_pos (t : ℕ) : 0 < rsNormalization t := by
  simp only [rsNormalization]
  positivity

/-- Exact normalized energy of the two slowly varying modes. -/
theorem normalized_energy (t : ℕ) (x : ℝ) :
    ‖normalizedPDerivative 0 t x‖ ^ 2 +
      ‖normalizedQDerivative 0 t x‖ ^ 2 = 1 := by
  have henergy := rudinShapiro_energy t (norm_unitPoint (x / evenT t))
  have hEpos : (0 : ℝ) < (2 ^ (t + 1) : ℝ) := by positivity
  have hspos : 0 < Real.sqrt (2 ^ (t + 1) : ℝ) := Real.sqrt_pos.2 hEpos
  have hsquare := Real.sq_sqrt hEpos.le
  simp only [normalizedPDerivative, normalizedQDerivative, pow_zero, one_mul,
    Function.iterate_zero_apply, norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (rsNormalization_pos t)]
  rw [show
    (rsNormalization t * 1 * ‖(rudinShapiroP t).eval (unitPoint (x / evenT t))‖) ^ 2 +
      (rsNormalization t * 1 * ‖(rudinShapiroQ t).eval (unitPoint (x / evenT t))‖) ^ 2 =
      rsNormalization t ^ 2 *
        (‖(rudinShapiroP t).eval (unitPoint (x / evenT t))‖ ^ 2 +
          ‖(rudinShapiroQ t).eval (unitPoint (x / evenT t))‖ ^ 2) by ring,
    henergy]
  simp only [rsNormalization]
  field_simp
  exact hsquare.symm

private theorem normalizedDerivative_bound
    (p : Polynomial ℂ) (t r : ℕ) (x : ℝ)
    (hdeg : p.natDegree ≤ 2 ^ t)
    (hcircle : ∀ z : ℂ, ‖z‖ = 1 →
      ‖p.eval z‖ ≤ Real.sqrt (2 ^ (t + 1) : ℝ)) :
    ‖(rsNormalization t : ℂ) *
        (Complex.I / (evenT t : ℝ)) ^ r *
        ((Erdos228.Bernstein.eulerDerivative^[r]) p).eval
          (unitPoint (x / evenT t))‖ ≤ (1 / 2 ^ 10 : ℝ) ^ r := by
  have heuler :=
    Erdos228.Bernstein.norm_iterate_eulerDerivative_eval_le_pow_mul_circleSup
      hdeg hcircle r (norm_unitPoint (x / evenT t))
  have hTnat : 0 < evenT t := by simp [evenT]
  have hTpos : (0 : ℝ) < evenT t := by exact_mod_cast hTnat
  have hspos : 0 < Real.sqrt (2 ^ (t + 1) : ℝ) := by positivity
  have hpowcast : ((2 ^ t : ℕ) : ℝ) / evenT t = 1 / 2 ^ 10 := by
    rw [evenT_eq_pow_mul]
    push_cast
    field_simp
    norm_num
  have hnonneg : 0 ≤ (1 / (evenT t : ℝ)) ^ r := by positivity
  calc
    ‖(rsNormalization t : ℂ) *
        (Complex.I / (evenT t : ℝ)) ^ r *
        ((Erdos228.Bernstein.eulerDerivative^[r]) p).eval
          (unitPoint (x / evenT t))‖ =
      rsNormalization t * (1 / (evenT t : ℝ)) ^ r *
        ‖((Erdos228.Bernstein.eulerDerivative^[r]) p).eval
          (unitPoint (x / evenT t))‖ := by
      rw [norm_mul, norm_mul, norm_pow, norm_div, Complex.norm_I]
      simp only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (rsNormalization_pos t), abs_of_pos hTpos, one_div]
    _ ≤ rsNormalization t * (1 / (evenT t : ℝ)) ^ r *
        (((2 ^ t : ℕ) : ℝ) ^ r * Real.sqrt (2 ^ (t + 1) : ℝ)) := by
      exact mul_le_mul_of_nonneg_left heuler
        (mul_nonneg (rsNormalization_pos t).le hnonneg)
    _ = (((2 ^ t : ℕ) : ℝ) / evenT t) ^ r := by
      rw [rsNormalization]
      field_simp
      ring
    _ = (1 / 2 ^ 10 : ℝ) ^ r := by rw [hpowcast]

theorem norm_normalizedPDerivative_le (r t : ℕ) (x : ℝ) :
    ‖normalizedPDerivative r t x‖ ≤ (1 / 2 ^ 10 : ℝ) ^ r := by
  apply normalizedDerivative_bound (rudinShapiroP t) t r x
  · rw [natDegree_rudinShapiroP]
    exact Nat.sub_le _ _
  · intro z hz
    exact norm_eval_rudinShapiroP_le t hz

theorem norm_normalizedQDerivative_le (r t : ℕ) (x : ℝ) :
    ‖normalizedQDerivative r t x‖ ≤ (1 / 2 ^ 10 : ℝ) ^ r := by
  apply normalizedDerivative_bound (rudinShapiroQ t) t r x
  · rw [natDegree_rudinShapiroQ]
    exact Nat.sub_le _ _
  · intro z hz
    exact norm_eval_rudinShapiroQ_le t hz

/-- The normalized function rescales exactly to `evenCosine`. -/
theorem evenCosine_eq_normalizedH (t : ℕ) (theta : ℝ) :
    evenCosine t theta =
      Real.sqrt (2 ^ (t + 1) : ℝ) * (normalizedH t (2 * evenT t * theta)).re := by
  have hTnat : 0 < evenT t := by simp [evenT]
  have hT : (evenT t : ℝ) ≠ 0 := by exact_mod_cast hTnat.ne'
  have hs : Real.sqrt (2 ^ (t + 1) : ℝ) ≠ 0 := by positivity
  have hdiv : (2 * (evenT t : ℝ) * theta) / evenT t = 2 * theta := by
    field_simp [hT]
  have hphase₁ : unitPoint (2 * (evenT t : ℝ) * theta) =
      unitPoint (2 * theta) ^ evenT t := by
    simp only [unitPoint, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hphase₂ : unitPoint (2 * (2 * (evenT t : ℝ) * theta)) =
      unitPoint (2 * theta) ^ (2 * evenT t) := by
    simp only [unitPoint, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [evenCosine_eq]
  simp only [normalizedH, normalizedPDerivative, normalizedQDerivative, pow_zero,
    one_mul, mul_one, Function.iterate_zero_apply, hdiv, hphase₁, hphase₂, rsNormalization]
  rw [show
    unitPoint (2 * theta) ^ evenT t *
          ((((Real.sqrt (2 ^ (t + 1) : ℝ))⁻¹ : ℝ) : ℂ) *
            (rudinShapiroP t).eval (unitPoint (2 * theta))) +
      unitPoint (2 * theta) ^ (2 * evenT t) *
          ((((Real.sqrt (2 ^ (t + 1) : ℝ))⁻¹ : ℝ) : ℂ) *
            (rudinShapiroQ t).eval (unitPoint (2 * theta))) =
      (((Real.sqrt (2 ^ (t + 1) : ℝ))⁻¹ : ℝ) : ℂ) *
        (unitPoint (2 * theta) ^ evenT t *
            (rudinShapiroP t).eval (unitPoint (2 * theta)) +
          unitPoint (2 * theta) ^ (2 * evenT t) *
            (rudinShapiroQ t).eval (unitPoint (2 * theta))) by ring]
  simp only [Complex.mul_re, Complex.inv_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.normSq_ofReal, zero_mul, sub_zero]
  field_simp

/-! ## Symmetries of the cosine block -/

private theorem cosineBlock_coeff_im_eq_zero {t k : ℕ}
    (hk : k ∈ (cosineBlockPolynomial t).support) :
    ((cosineBlockPolynomial t).coeff k).im = 0 := by
  rw [support_cosineBlockPolynomial] at hk
  rw [mem_evenCPrime] at hk
  rcases hk with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · rw [coeff_cosineBlockPolynomial_first t j hj]
    rcases coeff_rudinShapiroP_eq_one_or_neg_one hj with h | h <;> simp [h]
  · rw [coeff_cosineBlockPolynomial_second t j hj]
    rcases coeff_rudinShapiroQ_eq_one_or_neg_one hj with h | h <;> simp [h]

/-- The cosine block is a real cosine sum over the support of its defining
polynomial. -/
theorem evenCosine_eq_sum_cos (t : ℕ) (theta : ℝ) :
    evenCosine t theta =
      ∑ k ∈ (cosineBlockPolynomial t).support,
        ((cosineBlockPolynomial t).coeff k).re * Real.cos (k * (2 * theta)) := by
  classical
  rw [evenCosine, Polynomial.eval_eq_sum, Polynomial.sum_def]
  change Complex.reLm
      (∑ k ∈ (cosineBlockPolynomial t).support,
        (cosineBlockPolynomial t).coeff k * unitPoint (2 * theta) ^ k) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hre : (unitPoint (2 * theta) ^ k).re = Real.cos (k * (2 * theta)) := by
    have h := congrArg Complex.re (Erdos228.unitPoint_pow (2 * theta) k)
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, mul_one, add_zero] using h
  change ((cosineBlockPolynomial t).coeff k * unitPoint (2 * theta) ^ k).re = _
  rw [Complex.mul_re, cosineBlock_coeff_im_eq_zero hk, zero_mul, sub_zero, hre]

@[simp] theorem evenCosine_neg (t : ℕ) (theta : ℝ) :
    evenCosine t (-theta) = evenCosine t theta := by
  classical
  rw [evenCosine_eq_sum_cos, evenCosine_eq_sum_cos]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  rw [show (k : ℝ) * (2 * -theta) = -((k : ℝ) * (2 * theta)) by ring,
    Real.cos_neg]

@[simp] theorem evenCosine_pi_sub (t : ℕ) (theta : ℝ) :
    evenCosine t (Real.pi - theta) = evenCosine t theta := by
  classical
  rw [evenCosine_eq_sum_cos, evenCosine_eq_sum_cos]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  rw [show (k : ℝ) * (2 * (Real.pi - theta)) =
      (k : ℝ) * (2 * Real.pi) - (k : ℝ) * (2 * theta) by ring,
    Real.cos_nat_mul_two_pi_sub]

@[simp] theorem evenCosine_sub_pi (t : ℕ) (theta : ℝ) :
    evenCosine t (theta - Real.pi) = evenCosine t theta := by
  rw [show theta - Real.pi = -(Real.pi - theta) by ring, evenCosine_neg,
    evenCosine_pi_sub]

/-! ## The seven-cell analytic lemma -/

/-- The conclusion of the Howell argument before rescaling back to the
`pi/n` grid. -/
def HasGoodCellInEverySeven (f : ℝ → ℝ) (eta : ℝ) : Prop :=
  ∀ a : ℝ, ∃ j : ℕ, j < 7 ∧
    ∀ x ∈ Icc (a + (j : ℝ) * eta) (a + ((j : ℝ) + 1) * eta),
    eta ^ 3 / 128 ≤ |f x|

/-- The complete seven-cell argument.  The four-derivative algebra supplies
`hlarge`; Bernstein supplies `hderiv`; Howell interpolation then prevents all
seven consecutive cells from containing a small value. -/
theorem hasGoodCellInEverySeven_of_derivative_bounds
    (f : ℝ → ℝ) (eta : ℝ)
    (heta : 0 < eta) (hetaSmall : eta < (1 : ℝ) / 2048)
    (hf : ContDiff ℝ 4 f)
    (hlarge : ∀ x, ∃ k : Fin 4, 1 / 4 ≤ |iteratedDeriv k f x|)
    (hderiv : ∀ r ≤ 4, ∀ x, |iteratedDeriv r f x| ≤ 18) :
    HasGoodCellInEverySeven f eta := by
  intro a
  by_contra hnone
  push_neg at hnone
  have hsample (j : Fin 7) :
      ∃ x ∈ Icc (a + (j : ℕ) * eta) (a + ((j : ℕ) + 1) * eta),
        |f x| < eta ^ 3 / 128 := by
    exact hnone (j : ℕ) j.isLt
  let sample : Fin 7 → ℝ := fun j ↦ Classical.choose (hsample j)
  have sample_mem (j : Fin 7) :
      sample j ∈ Icc (a + (j : ℕ) * eta) (a + ((j : ℕ) + 1) * eta) :=
    (Classical.choose_spec (hsample j)).1
  have sample_small (j : Fin 7) : |f (sample j)| < eta ^ 3 / 128 :=
    (Classical.choose_spec (hsample j)).2
  obtain ⟨k, hklarge⟩ := hlarge (sample 0)
  by_cases hk0 : (k : ℕ) = 0
  · have hsmall := sample_small (0 : Fin 7)
    simp only [hk0, iteratedDeriv_zero] at hklarge
    have hetaOne : eta < 1 := lt_trans hetaSmall (by norm_num)
    have hetaCube : eta ^ 3 < 1 := pow_lt_one₀ heta.le hetaOne (by norm_num)
    norm_num at hsmall hklarge
    nlinarith
  · have hk₁ : 1 ≤ (k : ℕ) := Nat.one_le_iff_ne_zero.mpr hk0
    have hk₃ : (k : ℕ) ≤ 3 := by omega
    let node : Fin ((k : ℕ) + 1) → ℝ := fun i ↦
      sample ⟨2 * (i : ℕ), by omega⟩
    have hnode_mem (i : Fin ((k : ℕ) + 1)) :
        node i ∈ Icc (a + (2 * (i : ℕ)) * eta)
          (a + (2 * (i : ℕ) + 1) * eta) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        (sample_mem ⟨2 * (i : ℕ), by omega⟩)
    have hnode_mono : StrictMono node := by
      intro i j hij
      have hi := hnode_mem i
      have hj := hnode_mem j
      have hijNat : (i : ℕ) < (j : ℕ) := by exact_mod_cast hij
      dsimp only [node]
      have hgap : a + (2 * (i : ℕ) + 1) * eta <
          a + (2 * (j : ℕ)) * eta := by
        have : (2 * (i : ℕ) + 1 : ℝ) < 2 * (j : ℕ) := by exact_mod_cast (by omega)
        nlinarith
      exact hi.2.trans_lt (hgap.trans_le hj.1)
    have hnode_sep : ∀ i j, i ≠ j → eta ≤ |node i - node j| := by
      intro i j hij
      rcases lt_or_gt_of_ne hij with hijlt | hjilt
      · have hi := hnode_mem i
        have hj := hnode_mem j
        have hijNat : (i : ℕ) < (j : ℕ) := by exact_mod_cast hijlt
        rw [abs_of_nonpos (sub_nonpos.mpr (hnode_mono hijlt).le)]
        dsimp only [node] at hi hj ⊢
        have hgap : a + (2 * (i : ℕ) + 1) * eta + eta ≤
            a + (2 * (j : ℕ)) * eta := by
          have : (2 * (i : ℕ) + 2 : ℝ) ≤ 2 * (j : ℕ) := by exact_mod_cast (by omega)
          nlinarith
        linarith [hi.2, hj.1]
      · have hi := hnode_mem i
        have hj := hnode_mem j
        have hjiNat : (j : ℕ) < (i : ℕ) := by exact_mod_cast hjilt
        rw [abs_of_nonneg (sub_nonneg.mpr (hnode_mono hjilt).le)]
        dsimp only [node] at hi hj ⊢
        have hgap : a + (2 * (j : ℕ) + 1) * eta + eta ≤
            a + (2 * (i : ℕ)) * eta := by
          have : (2 * (j : ℕ) + 2 : ℝ) ≤ 2 * (i : ℕ) := by exact_mod_cast (by omega)
          nlinarith
        linarith [hj.2, hi.1]
    have hnode_dist (i : Fin ((k : ℕ) + 1)) :
        |node i - sample 0| ≤ 7 * eta := by
      have hi := hnode_mem i
      have h0 := sample_mem (0 : Fin 7)
      have hleft : sample 0 ≤ node i := by
        by_cases hi0 : (i : ℕ) = 0
        · apply le_of_eq
          have hieq : i = 0 := Fin.ext hi0
          subst i
          apply congrArg sample
          exact Fin.ext rfl
        · have hiPos : 1 ≤ (i : ℕ) := Nat.one_le_iff_ne_zero.mpr hi0
          have hgap : a + eta ≤ a + (2 * (i : ℕ)) * eta := by
            have : (1 : ℝ) ≤ 2 * (i : ℕ) := by exact_mod_cast (by omega)
            nlinarith
          norm_num at h0
          exact h0.2.trans (hgap.trans hi.1)
      rw [abs_of_nonneg (sub_nonneg.mpr hleft)]
      have hik : (i : ℕ) ≤ (k : ℕ) := Nat.le_of_lt_succ i.isLt
      have hupper : node i ≤ a + 7 * eta := by
        calc
          node i ≤ a + (2 * (i : ℕ) + 1) * eta := hi.2
          _ ≤ a + 7 * eta := by
            have : (2 * (i : ℕ) + 1 : ℝ) ≤ 7 := by exact_mod_cast (by omega)
            nlinarith
      norm_num at h0
      linarith [h0.1]
    have hnode_value (i : Fin ((k : ℕ) + 1)) :
        |f (node i)| ≤ eta ^ 3 / 128 := by
      have hiLe : (i : ℕ) ≤ (k : ℕ) := Nat.le_of_lt_succ i.isLt
      have hkLt : (k : ℕ) < 4 := k.isLt
      have hidx : 2 * (i : ℕ) < 7 := by omega
      exact (sample_small ⟨2 * (i : ℕ), hidx⟩).le
    have hk4 : (k : ℕ) + 1 ≤ 4 := by omega
    have hquarter := Erdos228.Interpolation.howell_lt_quarter_of_nodes
      (k : ℕ) hk₁ hk₃ f node (sample 0) eta
      (hf.of_le (by exact_mod_cast hk4)) hnode_mono heta hetaSmall hnode_sep hnode_dist
      hnode_value
      (fun x ↦ hderiv ((k : ℕ) + 1) hk4 x)
    linarith

/-- A grid cell is bad if it contains a point at which the cosine coordinate
is strictly below the desired lower threshold. -/
def BadCell (n t : ℕ) (gamma : ℝ) (i : ℕ) : Prop :=
  ∃ theta ∈ Erdos228.Intervals.gridCell n i,
    |evenCosine t theta| < cosineThreshold n gamma

noncomputable instance instDecidablePredBadCell (n t : ℕ) (gamma : ℝ) :
    DecidablePred (BadCell n t gamma) := Classical.decPred _

/-- The maximal linear runs of bad cells in the period `[0,2*pi]`.
Endpoints are cell indices, so `(a,b)` denotes the real interval from
`a*pi/n` to `(b+1)*pi/n`. -/
noncomputable def dangerousRuns (n t : ℕ) (gamma : ℝ) : Finset (ℕ × ℕ) :=
  @Erdos228.Intervals.maximalBadRuns (2 * n) (BadCell n t gamma)
    (Classical.decPred _)

@[simp] theorem mem_dangerousRuns {n t : ℕ} {gamma : ℝ} {a b : ℕ} :
    (a, b) ∈ dangerousRuns n t gamma ↔
      Erdos228.Intervals.IsMaximalBadRun (2 * n) (BadCell n t gamma) a b := by
  classical
  exact Erdos228.Intervals.mem_maximalBadRuns

/-- The real interval represented by a run of cells. -/
def runInterval (n : ℕ) (I : ℕ × ℕ) : Set ℝ :=
  Icc (Erdos228.Intervals.gridPoint n I.1)
    (Erdos228.Intervals.gridPoint n (I.2 + 1))

/-- Endpoint pair corresponding to `runInterval`. -/
def runEndpoints (n : ℕ) (I : ℕ × ℕ) : Erdos228.OddSine.RealInterval :=
  (Erdos228.Intervals.gridPoint n I.1,
    Erdos228.Intervals.gridPoint n (I.2 + 1))

/-- The dangerous runs wholly contained in the first quadrant. -/
noncomputable def firstQuadrantRuns (n t : ℕ) (gamma : ℝ) : Finset (ℕ × ℕ) :=
  (dangerousRuns n t gamma).filter fun I ↦ 2 * (I.2 + 1) ≤ n

/-- First-quadrant intervals in the representation consumed by `OddSine`. -/
noncomputable def firstQuadrantIntervals (n t : ℕ) (gamma : ℝ) :
    Finset Erdos228.OddSine.RealInterval :=
  (firstQuadrantRuns n t gamma).image (runEndpoints n)

@[simp] theorem mem_firstQuadrantRuns {n t : ℕ} {gamma : ℝ} {I : ℕ × ℕ} :
    I ∈ firstQuadrantRuns n t gamma ↔
      I ∈ dangerousRuns n t gamma ∧ 2 * (I.2 + 1) ≤ n := by
  classical
  simp [firstQuadrantRuns]

theorem runEndpoints_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (runEndpoints n) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [runEndpoints, Prod.mk.injEq] at h
  have hstrict := Erdos228.Intervals.gridPoint_strictMono hn
  have hac : a = c := hstrict.injective h.1
  have hbd : b + 1 = d + 1 := hstrict.injective h.2
  simp only [Prod.mk.injEq]
  exact ⟨hac, Nat.succ.inj hbd⟩

theorem card_firstQuadrantIntervals {n t : ℕ} {gamma : ℝ} (hn : 0 < n) :
    (firstQuadrantIntervals n t gamma).card =
      (firstQuadrantRuns n t gamma).card := by
  classical
  exact Finset.card_image_of_injective _ (runEndpoints_injective hn)

/-- Membership in at least one dangerous run. -/
def InDangerousRuns (n t : ℕ) (gamma : ℝ) (theta : ℝ) : Prop :=
  ∃ I ∈ dangerousRuns n t gamma, theta ∈ runInterval n I

/-- Every point of a bad cell is covered by a maximal dangerous run. -/
theorem badCell_covered {n t i : ℕ} {gamma theta : ℝ}
    (hi : i < 2 * n) (hbad : BadCell n t gamma i)
    (htheta : theta ∈ Erdos228.Intervals.gridCell n i) :
    InDangerousRuns n t gamma theta := by
  classical
  obtain ⟨I, hI, hleft, hright⟩ :=
    Erdos228.Intervals.exists_mem_maximalBadRuns_containing hi hbad
  refine ⟨I, ?_, ?_⟩
  · simpa only [dangerousRuns] using hI
  · rcases I with ⟨a, b⟩
    simp only [runInterval, Erdos228.Intervals.gridCell, mem_Icc] at htheta ⊢
    have hn : 0 < n := by omega
    have hmono := Erdos228.Intervals.gridPoint_mono hn
    exact ⟨(hmono hleft).trans htheta.1, htheta.2.trans (hmono (by omega))⟩

/-- A point in a grid cell but outside all dangerous runs has the desired
cosine lower bound.  This is the exact complement estimate used after the
cells have been assembled into a circular family. -/
theorem abs_evenCosine_ge_threshold_of_not_dangerous
    {n t i : ℕ} {gamma theta : ℝ}
    (hi : i < 2 * n)
    (htheta : theta ∈ Erdos228.Intervals.gridCell n i)
    (hout : ¬InDangerousRuns n t gamma theta) :
    cosineThreshold n gamma ≤ |evenCosine t theta| := by
  by_contra hlt
  rw [not_le] at hlt
  exact hout (badCell_covered hi ⟨theta, htheta, hlt⟩ htheta)

/-- The seven-cell conclusion, isolated as the exact combinatorial statement
needed to make every dangerous interval short. -/
def SevenCellProperty (n t : ℕ) (gamma : ℝ) : Prop :=
  ∀ a, a + 7 ≤ 2 * n →
    ∃ j < 7, ¬BadCell n t gamma (a + j)

/-- Rescaling the normalized good-cell conclusion produces the combinatorial
seven-cell property for the original angular grid. -/
theorem sevenCellProperty_of_normalized_good
    {n t : ℕ} {gamma : ℝ} (hparam : Parameters n t gamma)
    (hgood : HasGoodCellInEverySeven (fun x ↦ (normalizedH t x).re)
      (2 * (evenT t : ℝ) * Real.pi / n)) :
    SevenCellProperty n t gamma := by
  intro a ha
  let eta : ℝ := 2 * (evenT t : ℝ) * Real.pi / n
  obtain ⟨j, hj, hcell⟩ := hgood (a * eta)
  refine ⟨j, hj, ?_⟩
  rintro ⟨theta, htheta, hsmall⟩
  let x : ℝ := 2 * evenT t * theta
  have hnR : (0 : ℝ) < n := by exact_mod_cast hparam.n_pos
  have hT : (0 : ℝ) < evenT t := by
    exact_mod_cast (show 0 < evenT t by simp [evenT])
  have hx : x ∈ Icc (a * eta + (j : ℝ) * eta)
      (a * eta + ((j : ℝ) + 1) * eta) := by
    rcases htheta with ⟨hthetaL, hthetaR⟩
    simp only [Erdos228.Intervals.gridCell, Erdos228.Intervals.gridPoint] at hthetaL hthetaR
    dsimp [x, eta]
    constructor <;> push_cast at * <;>
      (field_simp [ne_of_gt hnR] at hthetaL hthetaR ⊢ <;> nlinarith [Real.pi_pos])
  have hnorm : eta ^ 3 / 128 ≤ |(normalizedH t x).re| := by
    simpa [eta] using hcell x hx
  have hsqrt : 0 ≤ Real.sqrt (2 ^ (t + 1) : ℝ) := Real.sqrt_nonneg _
  have hlower : cosineThreshold n gamma ≤
      Real.sqrt (2 ^ (t + 1) : ℝ) * |(normalizedH t x).re| := by
    calc
      cosineThreshold n gamma ≤
          Real.sqrt (2 ^ (t + 1) : ℝ) * eta ^ 3 / 128 := by
        simpa [eta] using hparam.threshold_le_normalized_good
      _ ≤ Real.sqrt (2 ^ (t + 1) : ℝ) * |(normalizedH t x).re| := by
        have := mul_le_mul_of_nonneg_left hnorm hsqrt
        nlinarith
  have heq : |evenCosine t theta| =
      Real.sqrt (2 ^ (t + 1) : ℝ) * |(normalizedH t x).re| := by
    rw [evenCosine_eq_normalizedH]
    dsimp [x]
    rw [abs_mul, abs_of_nonneg hsqrt]
  rw [← heq] at hlower
  exact (not_lt_of_ge hlower) hsmall

/-- A maximal run has at most six cells as soon as every block of seven
cells contains a good cell. -/
theorem dangerousRun_length_le_six {n t : ℕ} {gamma : ℝ}
    (hseven : SevenCellProperty n t gamma) {a b : ℕ}
    (hab : (a, b) ∈ dangerousRuns n t gamma) :
    b + 1 - a ≤ 6 := by
  classical
  rw [mem_dangerousRuns] at hab
  by_contra hlong
  have hab7 : a + 7 ≤ b + 1 := by omega
  have hbN : b < 2 * n := hab.2.1
  have ha7N : a + 7 ≤ 2 * n := by omega
  obtain ⟨j, hj, hgood⟩ := hseven a ha7N
  apply hgood
  exact hab.2.2.1 (a + j) (Finset.mem_range.mpr (by omega)) (by omega) (by omega)

/-- Consequently each represented real interval has length at most
`6*pi/n`. -/
theorem dangerousRun_width_le {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n) (hseven : SevenCellProperty n t gamma) {I : ℕ × ℕ}
    (hI : I ∈ dangerousRuns n t gamma) :
    Erdos228.Intervals.gridPoint n (I.2 + 1) -
        Erdos228.Intervals.gridPoint n I.1 ≤ 6 * Real.pi / n := by
  rcases I with ⟨a, b⟩
  have hlen := dangerousRun_length_le_six hseven hI
  simp only [Erdos228.Intervals.gridPoint]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hba : a ≤ b + 1 := by
    rw [mem_dangerousRuns] at hI
    exact hI.1.trans (Nat.le_succ b)
  have hcast : ((b + 1 - a : ℕ) : ℝ) ≤ 6 := by exact_mod_cast hlen
  rw [Nat.cast_sub hba] at hcast
  rw [← sub_div]
  apply (div_le_div_iff_of_pos_right hnR).2
  nlinarith [Real.pi_pos]

/-- Distinct maximal runs have at least one grid step between their interiors.
The statement is oriented; swapping the two runs gives the other case. -/
theorem dangerousRuns_separated {n t : ℕ} {gamma : ℝ} {a b c d : ℕ}
    (h₁ : (a, b) ∈ dangerousRuns n t gamma)
    (h₂ : (c, d) ∈ dangerousRuns n t gamma)
    (hbc : b < c) : b + 2 ≤ c := by
  classical
  rw [mem_dangerousRuns] at h₁ h₂
  by_contra h
  have hc : c = b + 1 := by omega
  have hcN : c < 2 * n := h₂.1.trans_lt h₂.2.1
  have hbadc := h₂.2.2.1 c (Finset.mem_range.mpr hcN) le_rfl h₂.1
  rcases h₁.2.2.2.2 with hright | hgood
  · rw [hc, hright] at hcN
    omega
  · exact hgood (by simpa [hc] using hbadc)

/-! ## Conversion to the odd-sine interval interface -/

/-- The remaining two geometric estimates in the exact form required by
`OddSine.SuitableIntervalFamily`.  They are separated from the elementary
grid facts because the strict metric separation and exclusion of the axes
come from the analytic large-value neighborhoods. -/
structure GeometricCertificate (n t : ℕ) (gamma : ℝ) : Prop where
  separated : Set.Pairwise
    (↑(firstQuadrantIntervals n t gamma) :
      Set Erdos228.OddSine.RealInterval)
    (fun I J ↦ ∀ x ∈ Icc I.1 I.2, ∀ y ∈ Icc J.1 J.2,
      Real.pi / n ≤ |x - y|)
  away_from_axes : ∀ I ∈ firstQuadrantIntervals n t gamma,
    100 * Real.pi / n ≤ I.1 ∧
      I.2 ≤ Real.pi / 2 - 100 * Real.pi / n

/-- The maximal first-quadrant bad runs, equipped with the analytic
separation certificate, form exactly an `OddSine.SuitableIntervalFamily`. -/
def suitableIntervalFamilyOfDangerousRuns
    {n t : ℕ} {gamma : ℝ} (hn : 0 < n)
    (hseven : SevenCellProperty n t gamma)
    (hgeom : GeometricCertificate n t gamma) :
    Erdos228.OddSine.SuitableIntervalFamily n where
  base := firstQuadrantIntervals n t gamma
  ordered := by
    intro I hI
    classical
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    rw [mem_firstQuadrantRuns] at hJ
    rcases J with ⟨a, b⟩
    simp only [runEndpoints]
    apply Erdos228.Intervals.gridPoint_mono hn
    rw [mem_dangerousRuns] at hJ
    exact Nat.le_succ_of_le hJ.1.1
  nondegenerate := by
    intro I hI
    classical
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    rw [mem_firstQuadrantRuns] at hJ
    rcases J with ⟨a, b⟩
    simp only [runEndpoints]
    apply Erdos228.Intervals.gridPoint_strictMono hn
    rw [mem_dangerousRuns] at hJ
    exact Nat.lt_succ_of_le hJ.1.1
  in_first_quadrant := by
    intro I hI
    classical
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    rw [mem_firstQuadrantRuns] at hJ
    rcases J with ⟨a, b⟩
    simp only [runEndpoints]
    constructor
    · exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) Real.pi_pos.le)
        (Nat.cast_nonneg _)
    · have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hidx : (2 * (b + 1) : ℝ) ≤ n := by exact_mod_cast hJ.2
      simp only [Erdos228.Intervals.gridPoint]
      norm_num [Nat.cast_add]
      apply (div_le_iff₀ hnR).2
      have hmul := mul_le_mul_of_nonneg_right hidx Real.pi_pos.le
      norm_num [Nat.cast_add] at hmul
      nlinarith
  grid_endpoints := by
    intro I hI
    classical
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    rcases J with ⟨a, b⟩
    exact ⟨a, b + 1, by simp [runEndpoints, Erdos228.Intervals.gridPoint],
      by simp [runEndpoints, Erdos228.Intervals.gridPoint]⟩
  short := by
    intro I hI
    classical
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    rw [mem_firstQuadrantRuns] at hJ
    simpa only [runEndpoints] using dangerousRun_width_le hn hseven hJ.1
  separated := hgeom.separated
  away_from_axes := hgeom.away_from_axes

/-- Membership in one of the first-quadrant base intervals. -/
def InBaseFamily {n : ℕ} (F : Erdos228.OddSine.SuitableIntervalFamily n)
    (theta : ℝ) : Prop :=
  ∃ I ∈ F.base, Erdos228.OddSine.InInterval I theta

/-- The four defining symmetries of `IsDangerous` extend a lower bound from
the first quadrant to the bounded fundamental interval used by the final
assembly. -/
theorem lower_on_fundamental_of_lower_off_base
    {n t : ℕ} {gamma : ℝ} (F : Erdos228.OddSine.SuitableIntervalFamily n)
    (hfirst : ∀ theta ∈ Icc (0 : ℝ) (Real.pi / 2),
      ¬InBaseFamily F theta →
        cosineThreshold n gamma ≤ |evenCosine t theta|) :
    ∀ theta ∈ Icc (-Real.pi / 2) (3 * Real.pi / 2),
      ¬Erdos228.OddSine.IsDangerous F theta →
        cosineThreshold n gamma ≤ |evenCosine t theta| := by
  intro theta htheta hout
  rcases htheta with ⟨hthetaLower, hthetaUpper⟩
  by_cases h0 : theta ≤ 0
  · have hphi : -theta ∈ Icc (0 : ℝ) (Real.pi / 2) := by
      constructor <;> linarith
    have hbase : ¬InBaseFamily F (-theta) := by
      rintro ⟨I, hI, hmem⟩
      exact hout ⟨I, hI, Or.inr (Or.inl hmem)⟩
    simpa using hfirst (-theta) hphi hbase
  · have htheta0 : 0 ≤ theta := le_of_not_ge h0
    by_cases hhalf : theta ≤ Real.pi / 2
    · exact hfirst theta ⟨htheta0, hhalf⟩ fun hbase ↦ by
        rcases hbase with ⟨I, hI, hmem⟩
        exact hout ⟨I, hI, Or.inl hmem⟩
    · have hhalf' : Real.pi / 2 ≤ theta := le_of_not_ge hhalf
      by_cases hpi : theta ≤ Real.pi
      · have hphi : Real.pi - theta ∈ Icc (0 : ℝ) (Real.pi / 2) := by
          constructor <;> linarith
        have hbase : ¬InBaseFamily F (Real.pi - theta) := by
          rintro ⟨I, hI, hmem⟩
          exact hout ⟨I, hI, Or.inr (Or.inr (Or.inl hmem))⟩
        simpa using hfirst (Real.pi - theta) hphi hbase
      · have hpi' : Real.pi ≤ theta := le_of_not_ge hpi
        have hphi : theta - Real.pi ∈ Icc (0 : ℝ) (Real.pi / 2) := by
          constructor <;> linarith
        have hbase : ¬InBaseFamily F (theta - Real.pi) := by
          rintro ⟨I, hI, hmem⟩
          exact hout ⟨I, hI, Or.inr (Or.inr (Or.inr hmem))⟩
        simpa using hfirst (theta - Real.pi) hphi hbase

/-- The dangerous set generated by the converted family contains every
first-quadrant low-cosine point once the maximal-run covering fact has been
expressed at the interval level. -/
theorem isDangerous_of_firstQuadrantInterval
    {n t : ℕ} {gamma theta : ℝ} (hn : 0 < n)
    (hseven : SevenCellProperty n t gamma)
    (hgeom : GeometricCertificate n t gamma)
    (hcover : ∃ I ∈ firstQuadrantIntervals n t gamma,
      Erdos228.OddSine.InInterval I theta) :
    Erdos228.OddSine.IsDangerous
      (suitableIntervalFamilyOfDangerousRuns hn hseven hgeom) theta := by
  rcases hcover with ⟨I, hI, htheta⟩
  exact ⟨I, hI, Or.inl htheta⟩

/-- Cardinality of the base family in the real form used by the first
discrepancy colouring. -/
theorem suitableFamily_base_card
    {n t : ℕ} {gamma : ℝ} (hn : 0 < n)
    (hseven : SevenCellProperty n t gamma)
    (hgeom : GeometricCertificate n t gamma) :
    (suitableIntervalFamilyOfDangerousRuns hn hseven hgeom).base.card =
      (firstQuadrantRuns n t gamma).card :=
  card_firstQuadrantIntervals hn

/-- A finite set of boundary contacts and a choice of one contact in each
change cell give the standard component-count estimate. -/
theorem card_dangerousRuns_le_two_mul_roots_add_one
    {n t : ℕ} {gamma : ℝ} (hn : 0 < n)
    (roots : Finset ℝ) (rootOf : ℕ → ℝ)
    (hroot : ∀ i ∈ Erdos228.Intervals.changeIndices (2 * n) (BadCell n t gamma),
      rootOf i ∈ roots)
    (hcell : ∀ i ∈ Erdos228.Intervals.changeIndices (2 * n) (BadCell n t gamma),
      rootOf i ∈ Erdos228.Intervals.gridCell n i) :
    (dangerousRuns n t gamma).card ≤ 2 * roots.card + 1 := by
  classical
  simpa only [dangerousRuns] using
    (Erdos228.Intervals.card_maximalBadRuns_le_two_mul_card_roots_add_one
      hn (BadCell n t gamma) roots rootOf hroot hcell)

/-- The fully assembled finite-grid conclusion.  The two analytic inputs are
made explicit: `hseven` is supplied by the normalized four-derivative/Howell
argument, while `roots,rootOf` are supplied by the Laurent-polynomial root
count.  Everything after those inputs is finite interval bookkeeping. -/
theorem cosine_bad_interval_conclusion
    {n t : ℕ} {gamma : ℝ} (hparam : Parameters n t gamma)
    (hscale : 2 ^ (t + 3) ≤ n)
    (hseven : SevenCellProperty n t gamma)
    (roots : Finset ℝ) (rootOf : ℕ → ℝ)
    (hroot : ∀ i ∈ Erdos228.Intervals.changeIndices (2 * n) (BadCell n t gamma),
      rootOf i ∈ roots)
    (hcell : ∀ i ∈ Erdos228.Intervals.changeIndices (2 * n) (BadCell n t gamma),
      rootOf i ∈ Erdos228.Intervals.gridCell n i) :
    (∀ theta, |evenCosine t theta| ≤ Real.sqrt n) ∧
    (∀ I ∈ dangerousRuns n t gamma,
      Erdos228.Intervals.gridPoint n (I.2 + 1) -
        Erdos228.Intervals.gridPoint n I.1 ≤ 6 * Real.pi / n) ∧
    (dangerousRuns n t gamma).card ≤ 2 * roots.card + 1 ∧
    (∀ {i theta}, i < 2 * n →
      theta ∈ Erdos228.Intervals.gridCell n i →
      ¬InDangerousRuns n t gamma theta →
      cosineDelta gamma * Real.sqrt n ≤ |evenCosine t theta|) := by
  refine ⟨fun theta ↦ abs_evenCosine_le_sqrt n t hscale theta, ?_, ?_, ?_⟩
  · intro I hI
    exact dangerousRun_width_le hparam.n_pos hseven hI
  · exact card_dangerousRuns_le_two_mul_roots_add_one hparam.n_pos roots rootOf hroot hcell
  · intro i theta hi htheta hout
    exact abs_evenCosine_ge_threshold_of_not_dangerous hi htheta hout

end

end Erdos228.CosineConstruction
