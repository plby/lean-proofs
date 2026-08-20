/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos407.AdelicMinimaIndividual
import ErdosProblems.Erdos407.AdelicMinimaUpper

/-!
# Uniform logarithmic bounds for adelic successive minima

The upper adapted certificate has a fixed product constant.  On a fixed
compact interval of local exponents, the restricted product formula gives a
uniform polynomial lower bound for every individual minimum.  Dividing the
upper product estimate by the other individual lower bounds then gives a
uniform polynomial upper bound.  This file converts those two estimates into
the fixed base-`Q` interval used by the finite exterior-label argument.
-/

namespace Erdos407.PadicSubspace

open scoped BigOperators
open HeightBoxes

namespace AdelicMinimaLogBounds

open AdelicMinima AdelicMinimaUpper

noncomputable section

/-- The base-`Q` exponent, duplicated here in the acyclic minima layer.  It is
definitionally equal to `ExteriorFinal.logarithmicExponent`, so endpoint code
can consume the theorems below with `change`. -/
noncomputable def logarithmicExponent (Q : ℕ) (a : ℝ) : ℝ :=
  Real.log a / Real.log (Q : ℝ)

theorem logarithmicExponent_mono {Q : ℕ} (hQ : 1 < Q)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    logarithmicExponent Q a ≤ logarithmicExponent Q b := by
  unfold logarithmicExponent
  apply (div_le_div_iff_of_pos_right
    (Real.log_pos (by exact_mod_cast hQ))).2
  exact Real.log_le_log ha hab

theorem logarithmicExponent_mul {Q : ℕ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    logarithmicExponent Q (a * b) =
      logarithmicExponent Q a + logarithmicExponent Q b := by
  unfold logarithmicExponent
  rw [Real.log_mul ha.ne' hb.ne']
  ring

theorem logarithmicExponent_div {Q : ℕ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    logarithmicExponent Q (a / b) =
      logarithmicExponent Q a - logarithmicExponent Q b := by
  unfold logarithmicExponent
  rw [Real.log_div ha.ne' hb.ne']
  ring

theorem logarithmicExponent_pow {Q m : ℕ} {a : ℝ} :
    logarithmicExponent Q (a ^ m) =
      m * logarithmicExponent Q a := by
  unfold logarithmicExponent
  rw [Real.log_pow]
  ring

theorem logarithmicExponent_rpow {Q : ℕ} (hQ : 1 < Q) (a : ℝ) :
    logarithmicExponent Q ((Q : ℝ) ^ a) = a := by
  have hQr : 0 < (Q : ℝ) := by positivity
  have hlogQ : Real.log (Q : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hQ)).ne'
  unfold logarithmicExponent
  rw [Real.log_rpow hQr]
  exact mul_div_cancel_right₀ a hlogQ

theorem abs_logarithmicExponent_le_of_two_le {Q : ℕ} (hQ : 2 ≤ Q)
    {a : ℝ} (_ha : 0 < a) :
    |logarithmicExponent Q a| ≤ |Real.log a| / Real.log 2 := by
  have hQone : 1 < Q := by omega
  have hlogQ : 0 < Real.log (Q : ℝ) :=
    Real.log_pos (by exact_mod_cast hQone)
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogTwoQ : Real.log (2 : ℝ) ≤ Real.log (Q : ℝ) := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast hQ
  rw [logarithmicExponent, abs_div, abs_of_pos hlogQ]
  exact div_le_div_of_nonneg_left (abs_nonneg _) hlogTwo hlogTwoQ

/-- Every minimum has the same restricted-product lower bound when all local
exponents are at most `3`. -/
theorem lambda_lower_fixed
    {n : ℕ} {L : LocalForms n} (hL : IsNonsingularFamily L)
    {Q : ℕ} (hQ : 1 ≤ Q) {c : LocalConstants n}
    (hc : ∀ v i, c v i ≤ 3)
    {U : ℝ} (A : UpperAdaptedBasisCertificate L Q c U) (j : Fin n) :
    (pointGlobalConstant L * (Q : ℝ) ^ (9 : ℝ))⁻¹ ≤
      A.toAdaptedBasisCertificate.lambda j := by
  have hj0 : A.toAdaptedBasisCertificate.point j ≠ 0 :=
    A.toAdaptedBasisCertificate.independent.ne_zero j
  have h := lambda_lower_of_local_bounds L hL hQ c
    (M := (3 : ℝ)) hc hj0 (A.toAdaptedBasisCertificate.sIntegral j)
    (A.toAdaptedBasisCertificate.lambda_pos j).le
    (A.toAdaptedBasisCertificate.local_bound j)
  norm_num at h ⊢
  exact h

/-- The lower endpoint used for all minima. -/
noncomputable def commonLower {n : ℕ} (L : LocalForms n) (Q : ℕ) : ℝ :=
  (pointGlobalConstant L * (Q : ℝ) ^ (9 : ℝ))⁻¹

theorem commonLower_pos {n : ℕ} (L : LocalForms n) {Q : ℕ}
    (hQ : 1 ≤ Q) : 0 < commonLower L Q := by
  unfold commonLower
  apply inv_pos.mpr
  apply mul_pos (pointGlobalConstant_pos L)
  apply Real.rpow_pos_of_pos
  exact_mod_cast Nat.zero_lt_of_lt hQ

/-- Removing one index from the product leaves at least the corresponding
power of the common lower endpoint. -/
theorem commonLower_pow_le_prod_erase
    {n : ℕ} {L : LocalForms n} (hL : IsNonsingularFamily L)
    {Q : ℕ} (hQ : 1 ≤ Q) {c : LocalConstants n}
    (hc : ∀ v i, c v i ≤ 3)
    {U : ℝ} (A : UpperAdaptedBasisCertificate L Q c U) (j : Fin n) :
    commonLower L Q ^ (n - 1) ≤
      ∏ i ∈ (Finset.univ.erase j), A.toAdaptedBasisCertificate.lambda i := by
  have hcard : (Finset.univ.erase j).card = n - 1 := by
    simp
  rw [← hcard, ← Finset.prod_const]
  apply Finset.prod_le_prod
  · intro i hi
    exact (commonLower_pos L hQ).le
  · intro i hi
    exact lambda_lower_fixed hL hQ hc A i

/-- A lower bound on the sum of the local exponents gives the coarse upper
power needed for the product of the minima. -/
theorem product_le_fixed_power
    {n : ℕ} {L : LocalForms n} {Q : ℕ} (hQ : 1 ≤ Q)
    {c : LocalConstants n} (hc : ∀ v i, (-5 : ℝ) ≤ c v i)
    {U : ℝ} (A : UpperAdaptedBasisCertificate L Q c U) :
    ∏ i, A.toAdaptedBasisCertificate.lambda i ≤
      U * (Q : ℝ) ^ (15 * n : ℝ) := by
  have hsum : -(∑ v, ∑ i, c v i) ≤ (15 * n : ℝ) := by
    have hinner (v : Place23) : (-(5 : ℝ) * n) ≤ ∑ i, c v i := by
      calc
        (-(5 : ℝ) * n) = ∑ _i : Fin n, (-5 : ℝ) := by
          simp
          ring
        _ ≤ ∑ i, c v i := Finset.sum_le_sum fun i _ ↦ hc v i
    have hall : (-(15 : ℝ) * n) ≤ ∑ v, ∑ i, c v i := by
      calc
        (-(15 : ℝ) * n) = ∑ _v : Place23, (-(5 : ℝ) * n) := by
          norm_num [Fin.sum_univ_succ]
          ring
        _ ≤ ∑ v, ∑ i, c v i := Finset.sum_le_sum fun v _ ↦ hinner v
    linarith
  exact (A.product_le_rpow_neg_sum hQ).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hQ) hsum)
      A.upperConstant_pos.le)

/-- Pointwise polynomial upper bound obtained by dividing the product bound
by the common lower bounds for the other `n-1` minima. -/
theorem lambda_le_fixed_expression
    {n : ℕ} {L : LocalForms n} (hL : IsNonsingularFamily L)
    {Q : ℕ} (hQ : 1 ≤ Q) {c : LocalConstants n}
    (hcLower : ∀ v i, (-5 : ℝ) ≤ c v i)
    (hcUpper : ∀ v i, c v i ≤ 3)
    {U : ℝ} (A : UpperAdaptedBasisCertificate L Q c U) (j : Fin n) :
    A.toAdaptedBasisCertificate.lambda j ≤
      (U * (Q : ℝ) ^ (15 * n : ℝ)) /
        commonLower L Q ^ (n - 1) := by
  have hlow := commonLower_pow_le_prod_erase hL hQ hcUpper A j
  have hprod := product_le_fixed_power hQ hcLower A
  have hfactor :
      A.toAdaptedBasisCertificate.lambda j *
          (∏ i ∈ Finset.univ.erase j,
            A.toAdaptedBasisCertificate.lambda i) =
        ∏ i, A.toAdaptedBasisCertificate.lambda i := by
    exact Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)
  have hmul : A.toAdaptedBasisCertificate.lambda j * commonLower L Q ^ (n - 1) ≤
      U * (Q : ℝ) ^ (15 * n : ℝ) := by
    calc
      A.toAdaptedBasisCertificate.lambda j * commonLower L Q ^ (n - 1) ≤
          A.toAdaptedBasisCertificate.lambda j *
            (∏ i ∈ Finset.univ.erase j,
              A.toAdaptedBasisCertificate.lambda i) :=
        mul_le_mul_of_nonneg_left hlow
          (A.toAdaptedBasisCertificate.lambda_pos j).le
      _ = ∏ i, A.toAdaptedBasisCertificate.lambda i := hfactor
      _ ≤ U * (Q : ℝ) ^ (15 * n : ℝ) := hprod
  exact (le_div_iff₀ (pow_pos (commonLower_pos L hQ) _)).2 hmul

/-- A convenient fixed upper bound for the absolute base-`Q` exponent of a
positive constant, valid for every integral `Q ≥ 2`. -/
noncomputable def fixedLogMagnitude (a : ℝ) : ℝ :=
  |Real.log a| / Real.log 2

theorem fixedLogMagnitude_nonneg (a : ℝ) :
    0 ≤ fixedLogMagnitude a := by
  unfold fixedLogMagnitude
  positivity

/-- The common lower endpoint has an exact base-`Q` exponent. -/
theorem logarithmicExponent_commonLower
    {n : ℕ} (L : LocalForms n) {Q : ℕ} (hQ : 1 < Q) :
    logarithmicExponent Q (commonLower L Q) =
      -logarithmicExponent Q (pointGlobalConstant L) - 9 := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast Nat.zero_lt_of_lt hQ
  have hC : 0 < pointGlobalConstant L := pointGlobalConstant_pos L
  unfold commonLower
  rw [inv_eq_one_div,
    logarithmicExponent_div (by norm_num : (0 : ℝ) < 1)
      (mul_pos hC (Real.rpow_pos_of_pos hQr _)),
    logarithmicExponent_mul hC (Real.rpow_pos_of_pos hQr _),
    logarithmicExponent_rpow hQ]
  simp [logarithmicExponent]
  ring

/-- Exact exponent of the coarse pointwise upper expression. -/
theorem logarithmicExponent_fixed_expression
    {n : ℕ} {L : LocalForms n} {Q : ℕ} (hQ : 1 < Q)
    {U : ℝ} (hU : 0 < U) :
    logarithmicExponent Q
        ((U * (Q : ℝ) ^ (15 * n : ℝ)) /
          commonLower L Q ^ (n - 1)) =
      logarithmicExponent Q U + (15 * n : ℝ) -
        (n - 1 : ℕ) * logarithmicExponent Q (commonLower L Q) := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast Nat.zero_lt_of_lt hQ
  have hLower : 0 < commonLower L Q :=
    commonLower_pos L hQ.le
  rw [logarithmicExponent_div
      (mul_pos hU (Real.rpow_pos_of_pos hQr _)) (pow_pos hLower _),
    logarithmicExponent_mul hU (Real.rpow_pos_of_pos hQr _),
    logarithmicExponent_rpow hQ,
    logarithmicExponent_pow]

/-- One fixed symmetric interval containing the logarithmic exponents of all
successive minima for local exponents in `[-5,3]`. -/
noncomputable def logarithmicBound {n : ℕ} (L : LocalForms n) : ℝ :=
  fixedLogMagnitude (upperConstant L) + 15 * n +
    n * (fixedLogMagnitude (pointGlobalConstant L) + 9) +
      fixedLogMagnitude (pointGlobalConstant L) + 9

theorem logarithmicBound_nonneg {n : ℕ} (L : LocalForms n) :
    0 ≤ logarithmicBound L := by
  unfold logarithmicBound
  have hU := fixedLogMagnitude_nonneg (upperConstant L)
  have hC := fixedLogMagnitude_nonneg (pointGlobalConstant L)
  have hn : (0 : ℝ) ≤ n := by positivity
  nlinarith

theorem logarithmicExponent_lower_bound
    {n : ℕ} {L : LocalForms n} (hL : IsNonsingularFamily L)
    {Q : ℕ} (hQ : 2 ≤ Q) {c : LocalConstants n}
    (hc : ∀ v i, c v i ≤ 3)
    {U : ℝ} (A : UpperAdaptedBasisCertificate L Q c U) (j : Fin n) :
    -(fixedLogMagnitude (pointGlobalConstant L) + 9) ≤
      logarithmicExponent Q (A.toAdaptedBasisCertificate.lambda j) := by
  have hQone : 1 < Q := by omega
  have hlower := lambda_lower_fixed hL (by omega) hc A j
  have hmono := logarithmicExponent_mono hQone
    (commonLower_pos L (by omega)) hlower
  rw [logarithmicExponent_commonLower L hQone] at hmono
  have habs :
      |logarithmicExponent Q (pointGlobalConstant L)| ≤
        fixedLogMagnitude (pointGlobalConstant L) := by
    simpa [fixedLogMagnitude] using
      abs_logarithmicExponent_le_of_two_le hQ (pointGlobalConstant_pos L)
  rw [abs_le] at habs
  exact le_trans (by linarith [habs.1]) hmono

theorem logarithmicExponent_upper_bound
    {n : ℕ} {L : LocalForms n} (hL : IsNonsingularFamily L)
    {Q : ℕ} (hQ : 2 ≤ Q) {c : LocalConstants n}
    (hcLower : ∀ v i, (-5 : ℝ) ≤ c v i)
    (hcUpper : ∀ v i, c v i ≤ 3)
    {U : ℝ} (hU : 0 < U)
    (A : UpperAdaptedBasisCertificate L Q c U) (j : Fin n) :
    logarithmicExponent Q (A.toAdaptedBasisCertificate.lambda j) ≤
      fixedLogMagnitude U + 15 * n +
        n * (fixedLogMagnitude (pointGlobalConstant L) + 9) := by
  have hQone : 1 < Q := by omega
  have hupper := lambda_le_fixed_expression hL (by omega)
    hcLower hcUpper A j
  have hExprPos : 0 <
      (U * (Q : ℝ) ^ (15 * n : ℝ)) /
        commonLower L Q ^ (n - 1) := by
    exact div_pos
      (mul_pos hU (Real.rpow_pos_of_pos (by positivity) _))
      (pow_pos (commonLower_pos L (by omega)) _)
  have hmono := logarithmicExponent_mono hQone
    (A.toAdaptedBasisCertificate.lambda_pos j) hupper
  rw [logarithmicExponent_fixed_expression hQone hU,
    logarithmicExponent_commonLower L hQone] at hmono
  have habsU : |logarithmicExponent Q U| ≤ fixedLogMagnitude U := by
    simpa [fixedLogMagnitude] using
      abs_logarithmicExponent_le_of_two_le hQ hU
  have habsC : |logarithmicExponent Q (pointGlobalConstant L)| ≤
      fixedLogMagnitude (pointGlobalConstant L) := by
    simpa [fixedLogMagnitude] using
      abs_logarithmicExponent_le_of_two_le hQ (pointGlobalConstant_pos L)
  rw [abs_le] at habsU habsC
  have hcast : ((n - 1 : ℕ) : ℝ) ≤ n := by
    exact_mod_cast Nat.sub_le n 1
  have hCnonneg :
      0 ≤ fixedLogMagnitude (pointGlobalConstant L) + 9 := by
    linarith [fixedLogMagnitude_nonneg (pointGlobalConstant L)]
  have hcoef : (0 : ℝ) ≤ (n - 1 : ℕ) := by positivity
  have hterm := mul_le_mul_of_nonneg_left habsC.2 hcoef
  calc
    logarithmicExponent Q (A.toAdaptedBasisCertificate.lambda j) ≤
        logarithmicExponent Q U + (15 * n : ℝ) -
          (n - 1 : ℕ) *
            (-logarithmicExponent Q (pointGlobalConstant L) - 9) := hmono
    _ ≤ fixedLogMagnitude U + 15 * n +
          (n - 1 : ℕ) *
            (fixedLogMagnitude (pointGlobalConstant L) + 9) := by
      linarith [habsU.2, hterm]
    _ ≤ fixedLogMagnitude U + 15 * n +
          n * (fixedLogMagnitude (pointGlobalConstant L) + 9) := by
      gcongr

/-- Certificate-level logarithmic range with the fixed cutoff `Q ≥ 2`.
The radius depends only on the fixed dimension and local forms, not on `Q`,
the exponent array, the certificate, or the chosen minimum. -/
theorem logarithmicExponent_mem_Icc
    {n : ℕ} {L : LocalForms n} (hL : IsNonsingularFamily L)
    {Q : ℕ} (hQ : 2 ≤ Q) {c : LocalConstants n}
    (hc : ∀ v i, c v i ∈ Set.Icc (-5 : ℝ) 3)
    (A : UpperAdaptedBasisCertificate L Q c (upperConstant L)) (j : Fin n) :
    logarithmicExponent Q (A.toAdaptedBasisCertificate.lambda j) ∈
      Set.Icc (-logarithmicBound L) (logarithmicBound L) := by
  constructor
  · have h := logarithmicExponent_lower_bound hL hQ
      (fun v i ↦ (hc v i).2) A j
    unfold logarithmicBound
    have hU : 0 ≤ fixedLogMagnitude (upperConstant L) :=
      fixedLogMagnitude_nonneg _
    have hn : (0 : ℝ) ≤ n := by positivity
    have hC : 0 ≤ fixedLogMagnitude (pointGlobalConstant L) :=
      fixedLogMagnitude_nonneg _
    linarith [mul_nonneg hn (by linarith :
      0 ≤ fixedLogMagnitude (pointGlobalConstant L) + 9)]
  · exact (logarithmicExponent_upper_bound hL hQ
      (fun v i ↦ (hc v i).1) (fun v i ↦ (hc v i).2)
      (upperConstant_pos L hL) A j).trans (by
        unfold logarithmicBound
        linarith [fixedLogMagnitude_nonneg (pointGlobalConstant L)])

/-- No-premise existence form of the certificate together with its fixed
logarithmic range. -/
theorem exists_upperAdaptedBasisCertificate_with_logarithmicBound
    {n : ℕ} (hn : 0 < n) (L : LocalForms n)
    (hL : IsNonsingularFamily L) {Q : ℕ} (hQ : 2 ≤ Q)
    (c : LocalConstants n)
    (hc : ∀ v i, c v i ∈ Set.Icc (-5 : ℝ) 3) :
    ∃ A : UpperAdaptedBasisCertificate L Q c (upperConstant L),
      ∀ j, logarithmicExponent Q
          (A.toAdaptedBasisCertificate.lambda j) ∈
        Set.Icc (-logarithmicBound L) (logarithmicBound L) := by
  have hQone : 1 ≤ Q := (by omega)
  obtain ⟨A⟩ := exists_upperAdaptedBasisCertificate hn L hL hQone c
  exact ⟨A, fun j ↦ logarithmicExponent_mem_Icc hL hQ hc A j⟩

end

end AdelicMinimaLogBounds

end Erdos407.PadicSubspace
