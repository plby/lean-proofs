import ErdosProblems.Erdos788.PrimeParameters
import ErdosProblems.Erdos788.DesignLengthBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Pointwise bounds for the chosen field and dimension

The hypotheses in `ParameterRegular` are elementary eventual inequalities.
They are separated from the finite construction so the final asymptotic
argument only has to establish them once.
-/

namespace Erdos788

def ParameterRegular (N : ℕ) : Prop :=
  0 < Real.log (N : ℝ) ∧
  2 ≤ Real.log (Real.log (N : ℝ)) ∧
  exponentCorrection N *
      (Real.log (Real.log (N : ℝ)) + Real.log 4) ≤ 1 ∧
  400000000 * exponentCorrection N ≤ 1

theorem parameterRegular_correction_pos {N : ℕ} (h : ParameterRegular N) :
    0 < exponentCorrection N :=
  exponentCorrection_pos h.1 (by linarith [h.2])

theorem parameterRegular_correction_le_one {N : ℕ} (h : ParameterRegular N) :
    exponentCorrection N ≤ 1 := by
  have hδ := parameterRegular_correction_pos h
  nlinarith [h.2.2.2]

theorem parameterRegular_log_mul_correction {N : ℕ}
    (h : ParameterRegular N) :
    2 ≤ Real.log (N : ℝ) * exponentCorrection N := by
  let L := Real.log (N : ℝ)
  let q := Real.log L
  let δ := exponentCorrection N
  have hL : 0 < L := h.1
  have hq : 2 ≤ q := h.2.1
  have hδ : 0 < δ := parameterRegular_correction_pos h
  have hδ1 : δ ≤ 1 := parameterRegular_correction_le_one h
  have hcube : δ ^ 3 = q / L := by
    simpa [L, q, δ] using!
      exponentCorrection_pow_three h.1 (by linarith [h.2.1])
  have hrel : L * δ ^ 3 = q := by
    rw [hcube]
    field_simp
  have hcubed_le : δ ^ 3 ≤ δ := by
    nlinarith [sq_nonneg δ]
  dsimp only [L, δ] at hL hδ hδ1 hrel hcubed_le ⊢
  nlinarith

theorem parameterDimension_le_log_mul_correction {N : ℕ}
    (h : ParameterRegular N) :
    ((parameterDimension N : ℕ) : ℝ) ≤
      Real.log (N : ℝ) * exponentCorrection N := by
  have hδ := parameterRegular_correction_pos h
  have hA := parameterRegular_log_mul_correction h
  have hnR : (1 : ℝ) < N :=
    (Real.log_pos_iff (by positivity : (0 : ℝ) ≤ N)).mp h.1
  have hn : 1 < N := by exact_mod_cast hnR
  have hrUpper := cast_parameterDimension_lt_log_div_add_one hn.le
  have hinv := one_div_log_parameterPrime_lt_correction h.1
    (by linarith [h.2.1])
  have hfrac : Real.log (N : ℝ) /
      (2 * Real.log (parameterPrime N)) <
        Real.log (N : ℝ) * exponentCorrection N / 2 := by
    have hhalf : 0 < Real.log (N : ℝ) / 2 :=
      div_pos h.1 (by norm_num)
    calc
      Real.log (N : ℝ) / (2 * Real.log (parameterPrime N)) =
          (Real.log (N : ℝ) / 2) *
            (1 / Real.log (parameterPrime N)) := by ring
      _ < (Real.log (N : ℝ) / 2) * exponentCorrection N :=
        mul_lt_mul_of_pos_left hinv hhalf
      _ = Real.log (N : ℝ) * exponentCorrection N / 2 := by ring
  linarith

theorem parameterDimension_le_log {N : ℕ} (h : ParameterRegular N) :
    ((parameterDimension N : ℕ) : ℝ) ≤ Real.log (N : ℝ) := by
  have hδ1 := parameterRegular_correction_le_one h
  have hr := parameterDimension_le_log_mul_correction h
  exact hr.trans (by
    calc
      Real.log (N : ℝ) * exponentCorrection N ≤
          Real.log (N : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hδ1 h.1.le
      _ = Real.log (N : ℝ) := by ring)

theorem log_parameterProduct_le_two_logPrime {N : ℕ}
    (h : ParameterRegular N) :
    Real.log ((parameterPrime N * parameterDimension N : ℕ) : ℝ) ≤
      2 * Real.log (parameterPrime N) := by
  have hδ := parameterRegular_correction_pos h
  have hnR : (1 : ℝ) < N :=
    (Real.log_pos_iff (by positivity : (0 : ℝ) ≤ N)).mp h.1
  have hn : 1 < N := by exact_mod_cast hnR
  have hrNat : 0 < parameterDimension N := parameterDimension_pos hn
  have hrR : (0 : ℝ) < parameterDimension N := by exact_mod_cast hrNat
  have hlogr : Real.log (parameterDimension N : ℝ) ≤
      Real.log (Real.log (N : ℝ)) := by
    apply Real.log_le_log hrR
    exact parameterDimension_le_log h
  have hqP := loglog_le_log_parameterPrime N
  have hpR : (0 : ℝ) < parameterPrime N := by
    exact_mod_cast (Nat.zero_lt_of_lt (two_lt_parameterPrime N))
  rw [Nat.cast_mul, Real.log_mul hpR.ne' hrR.ne']
  linarith

theorem log_parameterProduct_le_four_div_correction {N : ℕ}
    (h : ParameterRegular N) :
    Real.log ((parameterPrime N * parameterDimension N : ℕ) : ℝ) ≤
      4 / exponentCorrection N := by
  have hpLog := log_parameterPrime_le_two_div_correction h.1
    (by linarith [h.2.1]) h.2.2.1
  have htwice : 2 * Real.log (parameterPrime N) ≤
      4 / exponentCorrection N := by
    have := mul_le_mul_of_nonneg_left hpLog (by norm_num : (0 : ℝ) ≤ 2)
    calc
      2 * Real.log (parameterPrime N) ≤
          2 * (2 / exponentCorrection N) := this
      _ = 4 / exponentCorrection N := by ring
  exact (log_parameterProduct_le_two_logPrime h).trans htwice

/-- The strong design size is at most an explicit multiple of
`log N * exponentCorrection N`. -/
theorem chosenDesign_coordCard_le
    {N : ℕ} (h : ParameterRegular N)
    (C : ShortLinearCode (parameterPrime N) (2 * parameterDimension N)
      (trevisanEta (parameterPrime N) (parameterDimension N))) :
    (((SuffixDesign.build C.ell (parameterDimension N)).coordCard : ℕ) : ℝ) ≤
      100000000 * Real.log (N : ℝ) * exponentCorrection N := by
  let L := Real.log (N : ℝ)
  let q := Real.log L
  let δ := exponentCorrection N
  let r := parameterDimension N
  let u := Real.log ((parameterPrime N * r : ℕ) : ℝ)
  have hL : 0 < L := h.1
  have hq : 2 ≤ q := h.2.1
  have hδ : 0 < δ := parameterRegular_correction_pos h
  have hδ1 : δ ≤ 1 := parameterRegular_correction_le_one h
  have hr : (r : ℝ) ≤ L * δ := by
    simpa [L, δ, r] using! parameterDimension_le_log_mul_correction h
  have hr0Nat : 0 < r := by
    apply parameterDimension_pos
    have hnR : (1 : ℝ) < N :=
      (Real.log_pos_iff (by positivity : (0 : ℝ) ≤ N)).mp h.1
    exact_mod_cast hnR
  have hu : u ≤ 4 / δ := by
    simpa [u, δ, r] using! log_parameterProduct_le_four_div_correction h
  have hu1 : 1 ≤ u := by
    have hp3 : 3 ≤ parameterPrime N := by
      exact_mod_cast (two_lt_parameterPrime N)
    have hprod : 3 ≤ parameterPrime N * r := by
      simpa using! Nat.mul_le_mul hp3 (show 1 ≤ r by omega)
    dsimp [u]
    exact ((Real.lt_log_iff_exp_lt (by positivity)).2
      (Real.exp_one_lt_three.trans_le (by exact_mod_cast hprod))).le
  have hlogu : Real.log u ≤ q + Real.log 4 := by
    have hinvδL : δ⁻¹ ≤ L := by
      have hA := parameterRegular_log_mul_correction h
      have hone : (1 : ℝ) ≤ Real.log (N : ℝ) * exponentCorrection N :=
        (by norm_num : (1 : ℝ) ≤ 2).trans hA
      have hdiv : 1 / δ ≤ L := (div_le_iff₀ hδ).2 (by
        simpa [L, δ, mul_comm] using! hone)
      simpa [one_div] using! hdiv
    have hu4L : u ≤ 4 * L := by
      rw [div_eq_mul_inv] at hu
      nlinarith
    have hlog := Real.log_le_log (zero_lt_one.trans_le hu1) hu4L
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt hL)] at hlog
    simpa [q, add_comm] using! hlog
  have hcube : δ ^ 3 = q / L := by
    simpa [L, q, δ] using!
      exponentCorrection_pow_three h.1 (by linarith [h.2.1])
  have hrel : L * δ ^ 3 = q := by
    rw [hcube]
    field_simp
  let A := L * δ
  have hA0 : 0 < A := mul_pos hL hδ
  have hqAδ : q = A * δ ^ 2 := by
    dsimp [A]
    rw [hrel.symm]
    ring
  have hsqrtA : Real.sqrt A ≤ A * δ := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · calc
        A ≤ A * q :=
          by simpa using!
            (mul_le_mul_of_nonneg_left
              (by linarith : (1 : ℝ) ≤ q) hA0.le)
        _ = (A * δ) ^ 2 := by rw [hqAδ]; ring
  have hinvSqrt : δ⁻¹ * Real.sqrt A ≤ A := by
    calc
      δ⁻¹ * Real.sqrt A ≤ δ⁻¹ * (A * δ) :=
        mul_le_mul_of_nonneg_left hsqrtA (inv_nonneg.mpr hδ.le)
      _ = A := by field_simp
  have hsqrtr : Real.sqrt (r : ℝ) ≤ Real.sqrt A :=
    Real.sqrt_le_sqrt (by simpa [A] using! hr)
  have hfirst : 1000 * u * Real.sqrt (r : ℝ) ≤ 4000 * A := by
    have hu' : u ≤ 4 * δ⁻¹ := by simpa [div_eq_mul_inv] using! hu
    calc
      1000 * u * Real.sqrt (r : ℝ) ≤
          1000 * (4 * δ⁻¹) * Real.sqrt A := by gcongr
      _ = 4000 * (δ⁻¹ * Real.sqrt A) := by ring
      _ ≤ 4000 * A := by gcongr
  have hlog4 : Real.log 4 ≤ 2 := by
    have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
      have hraw :=
        Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at hraw
      exact hraw
    calc
      Real.log (4 : ℝ) = 2 * Real.log (2 : ℝ) := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        norm_num
      _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left hlog2 (by norm_num)
      _ = 2 := by norm_num
  have hfactor : 1 + Real.log u ≤ (5 / 2 : ℝ) * q := by
    nlinarith
  have hinvSqFactor : δ⁻¹ ^ 2 * (1 + Real.log u) ≤
      (5 / 2 : ℝ) * A := by
    have hidentity : δ⁻¹ ^ 2 * q = A := by
      rw [hqAδ]
      field_simp
    calc
      δ⁻¹ ^ 2 * (1 + Real.log u) ≤
          δ⁻¹ ^ 2 * ((5 / 2 : ℝ) * q) :=
        mul_le_mul_of_nonneg_left hfactor (sq_nonneg _)
      _ = (5 / 2 : ℝ) * A := by rw [← hidentity]; ring
  have hsecond : 2000000 * u ^ 2 * (1 + Real.log u) ≤
      80000000 * A := by
    have huSq : u ^ 2 ≤ (4 * δ⁻¹) ^ 2 := by
      gcongr
      simpa [div_eq_mul_inv] using! hu
    have hfactor0 : 0 ≤ 1 + Real.log u := by
      have := Real.log_nonneg hu1
      linarith
    calc
      2000000 * u ^ 2 * (1 + Real.log u) ≤
          2000000 * (4 * δ⁻¹) ^ 2 * (1 + Real.log u) := by
        gcongr
      _ = 32000000 * (δ⁻¹ ^ 2 * (1 + Real.log u)) := by ring
      _ ≤ 32000000 * ((5 / 2 : ℝ) * A) := by gcongr
      _ = 80000000 * A := by ring
  have hdesign := builtDesign_coordCard_le_log_bound
    (two_lt_parameterPrime N) hr0Nat C
  have hdesign' : (((SuffixDesign.build C.ell r).coordCard : ℕ) : ℝ) ≤
      1000 * u * Real.sqrt (r : ℝ) +
        2000000 * u ^ 2 * (1 + Real.log u) := by
    simpa [u, r] using! hdesign
  calc
    (((SuffixDesign.build C.ell (parameterDimension N)).coordCard : ℕ) : ℝ) ≤
        1000 * u * Real.sqrt (r : ℝ) +
          2000000 * u ^ 2 * (1 + Real.log u) := by
      simpa [r] using! hdesign'
    _ ≤ 100000000 * A := by linarith
    _ = 100000000 * Real.log (N : ℝ) * exponentCorrection N := by
      simp [A, L, δ]
      ring

end Erdos788
