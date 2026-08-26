import ErdosProblems.Erdos67b.MRGSA9SmallPrimeRestore

/-!
# Pointwise source A.9 at the Halász point

The global `MRArchimedeanNonpretentious` hypothesis in the original source
wrapper is stronger than the Euler argument needs.  This file records the
pointwise version.  It is useful when a minimizer dichotomy supplies a
distance lower bound only on the central Perron window.
-/

open scoped LSeries.notation

namespace Erdos67b.MRHalaszBands

noncomputable section

/-- The elementary left-line estimate at one frequency, assuming the
pretentious-distance lower bound only at that frequency. -/
theorem norm_LSeries_halaszPoint_le_one_add_log_mul_exp_of_distance
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {A X : ℕ} (hX : 1 < X) {t : ℝ}
    (hdist : (A : ℝ) ≤
      pretentiousDistSq f (archimedeanTwist t) X) :
    ‖LSeries f (Erdos67b.MRHalaszEuler.halaszPoint X t)‖ ≤
      (1 + Real.log (X : ℝ)) *
        Real.exp
          (-Real.exp (-1) * (A : ℝ) +
            3 * Erdos67b.EulerQuantitative.primeQuadraticConstant) := by
  let u : ℝ := Erdos67b.EulerResidue.taoExponent X
  let Z : ℝ := (riemannZeta (u : ℂ)).re
  have hu : 1 < u := by
    dsimp only [u]
    exact Erdos67b.EulerResidue.one_lt_taoExponent hX
  have hZpos : 0 < Z := by
    dsimp only [Z]
    exact (Complex.lt_def.mp (riemannZeta_pos_of_one_lt hu)).1
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast hX)
  have hZnorm : ‖riemannZeta (u : ℂ)‖ ≤ 1 + Real.log (X : ℝ) := by
    have hbase := Erdos67b.norm_riemannZeta_real_le_one_add_inv
      (sigma := (Real.log (X : ℝ))⁻¹) (inv_pos.mpr hlogX)
    dsimp only [u, Erdos67b.EulerResidue.taoExponent]
    simpa [inv_inv] using hbase
  have hZ : Z ≤ 1 + Real.log (X : ℝ) := by
    exact (le_abs_self Z).trans
      ((Complex.abs_re_le_norm _).trans hZnorm)
  have hbase :=
    Erdos67b.MRMultiplicativeEuler.norm_LSeries_halaszPoint_le_exp_logZeta_sub_pretentiousDistSq
      hmul hbound hX t
  have hbase' :
      ‖LSeries f (Erdos67b.MRHalaszEuler.halaszPoint X t)‖ ≤
        Real.exp
          (Real.log Z - Real.exp (-1) * (A : ℝ) +
            3 * Erdos67b.EulerQuantitative.primeQuadraticConstant) := by
    refine hbase.trans (Real.exp_le_exp.mpr ?_)
    have hexp : 0 ≤ Real.exp (-1) := (Real.exp_pos _).le
    dsimp only [u, Z]
    nlinarith
  calc
    ‖LSeries f (Erdos67b.MRHalaszEuler.halaszPoint X t)‖ ≤
        Real.exp
          (Real.log Z - Real.exp (-1) * (A : ℝ) +
            3 * Erdos67b.EulerQuantitative.primeQuadraticConstant) := hbase'
    _ = Z * Real.exp
          (-Real.exp (-1) * (A : ℝ) +
            3 * Erdos67b.EulerQuantitative.primeQuadraticConstant) := by
      rw [show Real.log Z - Real.exp (-1) * (A : ℝ) +
          3 * Erdos67b.EulerQuantitative.primeQuadraticConstant =
        Real.log Z +
          (-Real.exp (-1) * (A : ℝ) +
            3 * Erdos67b.EulerQuantitative.primeQuadraticConstant) by ring,
        Real.exp_add, Real.exp_log hZpos]
    _ ≤ (1 + Real.log (X : ℝ)) *
        Real.exp
          (-Real.exp (-1) * (A : ℝ) +
            3 * Erdos67b.EulerQuantitative.primeQuadraticConstant) := by
      exact mul_le_mul_of_nonneg_right hZ (Real.exp_pos _).le

/-- Widened source A.9 at a single frequency.  The distance hypothesis is
on the original coefficient; deletion of primes below `23` costs the same
factor two as in the global wrapper. -/
theorem norm_twoBlock_alternatingLow_deleteSmallPrimes_mul_high_le_wideHalaszPoint_of_distance
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (Q₂ Q₃ : ℕ → Prop) [DecidablePred Q₂] [DecidablePred Q₃]
    {y : ℕ} (hy : 23 ≤ y)
    (hdisj : ∀ p ∈ primesUpTo y, Q₂ p → Q₃ p → False)
    {A X : ℕ} (hX : 1 < X) {sigmaLow t : ℝ}
    (hdist : (A : ℝ) ≤
      pretentiousDistSq f (archimedeanTwist t) X)
    (hhalf : 1 / 2 ≤ sigmaLow)
    (hle : sigmaLow ≤ Erdos67b.EulerResidue.taoExponent X)
    (hsigmaLow : 1 - 3 / Real.log (y : ℝ) ≤ sigmaLow)
    (hgap : Erdos67b.EulerResidue.taoExponent X - sigmaLow ≤
      3 / Real.log (y : ℝ)) :
    let g := gsDeletePrimeBand f gsA9SmallPrime
    let sLow : ℂ := (sigmaLow : ℂ) + Complex.I * (t : ℂ)
    let sHigh : ℂ := Erdos67b.MRHalaszEuler.halaszPoint X t
    let Alt := LSeries (gsA9Low g y) sLow -
        LSeries (gsA9LowDeletion g Q₂ y) sLow -
        LSeries (gsA9LowDeletion g Q₃ y) sLow +
        LSeries (gsA9LowDeletion g (fun p ↦ Q₂ p ∨ Q₃ p) y) sLow
    ‖Alt * LSeries (gsA9High g y) sHigh‖ ≤
      gsA9WideSourceEulerConstant * (1 + Real.log (X : ℝ)) *
        Real.exp
          ((-Real.exp (-1) * ((A / 2 : ℕ) : ℝ) +
            3 * Erdos67b.EulerQuantitative.primeQuadraticConstant) / 2) := by
  dsimp only
  let g : ℕ → ℂ := gsDeletePrimeBand f gsA9SmallPrime
  let sLow : ℂ := (sigmaLow : ℂ) + Complex.I * (t : ℂ)
  let sHigh : ℂ := Erdos67b.MRHalaszEuler.halaszPoint X t
  let Alt : ℂ := LSeries (gsA9Low g y) sLow -
    LSeries (gsA9LowDeletion g Q₂ y) sLow -
    LSeries (gsA9LowDeletion g Q₃ y) sLow +
    LSeries (gsA9LowDeletion g (fun p ↦ Q₂ p ∨ Q₃ p) y) sLow
  let C : ℝ := gsA9WideSourceEulerConstant
  let q : ℝ := -Real.exp (-1) * ((A / 2 : ℕ) : ℝ) +
    3 * Erdos67b.EulerQuantitative.primeQuadraticConstant
  let B : ℝ := 1 + Real.log (X : ℝ)
  let D : ℝ := Real.exp (q / 2)
  have hsigmaHigh : 1 < Erdos67b.EulerResidue.taoExponent X :=
    Erdos67b.EulerResidue.one_lt_taoExponent hX
  have hsq :=
    norm_twoBlock_alternatingLow_deleteSmallPrimes_mul_high_sq_le_wideSource
      hmul hbound Q₂ Q₃ hy hdisj hhalf hle hsigmaLow hgap hsigmaHigh
      (t := t)
  have hmulG : IsMultiplicativeOnPositiveNat g :=
    gsDeletePrimeBand_isMultiplicativeOnPositiveNat hmul gsA9SmallPrime
  have hboundG : ∀ n, 0 < n → ‖g n‖ ≤ 1 := by
    intro n hn
    exact norm_gsDeletePrimeBand_le_one hbound gsA9SmallPrime hn
  have hdistG : (((A / 2 : ℕ) : ℝ)) ≤
      pretentiousDistSq g (archimedeanTwist t) X := by
    calc
      ((A / 2 : ℕ) : ℝ) ≤ (A : ℝ) / 2 := by
        simpa only [Nat.cast_ofNat] using (Nat.cast_div_le :
          ((A / 2 : ℕ) : ℝ) ≤ (A : ℝ) / (2 : ℝ))
      _ ≤ pretentiousDistSq g (archimedeanTwist t) X := by
        refine (div_le_div_of_nonneg_right hdist (by norm_num)).trans ?_
        exact half_pretentiousDistSq_le_deletePrimeBand
          (fun p hp ↦ hbound p hp.pos)
          (fun p hp ↦ by rw [norm_archimedeanTwist hp.pos])
          gsA9SmallPrime X
  have hL : ‖LSeries g sHigh‖ ≤ B * Real.exp q := by
    simpa only [g, sHigh, B, q] using
      norm_LSeries_halaszPoint_le_one_add_log_mul_exp_of_distance
        hmulG hboundG hX hdistG
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast hX)
  have hzeta : ‖riemannZeta (Erdos67b.EulerResidue.taoExponent X : ℂ)‖ ≤ B := by
    have h := Erdos67b.norm_riemannZeta_real_le_one_add_inv
      (sigma := (Real.log (X : ℝ))⁻¹) (inv_pos.mpr hlogX)
    simpa only [B, Erdos67b.EulerResidue.taoExponent, inv_inv] using h
  have hC0 : 0 ≤ C := by
    dsimp only [C, gsA9WideSourceEulerConstant]
    exact (Real.exp_pos _).le
  have hB0 : 0 ≤ B := by dsimp only [B]; linarith
  have hsq' : ‖Alt * LSeries (gsA9High g y) sHigh‖ ^ 2 ≤
      C * (B * Real.exp q) * B := by
    have hbase : ‖Alt * LSeries (gsA9High g y) sHigh‖ ^ 2 ≤
        C * ‖LSeries g sHigh‖ *
          ‖riemannZeta (Erdos67b.EulerResidue.taoExponent X : ℂ)‖ := by
      simpa only [g, sLow, sHigh, Alt, C,
        Erdos67b.MRHalaszEuler.halaszPoint] using hsq
    exact hbase.trans (by gcongr)
  have hC1 : 1 ≤ C := by
    unfold C gsA9WideSourceEulerConstant
    apply Real.one_le_exp
    have hshift0 : 0 ≤ gsA9WideSourceShiftConstant := by
      unfold gsA9WideSourceShiftConstant
      have hlogTwo : 0 < Real.log 2 := Real.log_pos one_lt_two
      have hdiv : 0 ≤ primeLogMertensConstant / Real.log 2 :=
        div_nonneg primeLogMertensConstant_nonneg hlogTwo.le
      exact mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le)
        (by linarith)
    exact add_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (Real.exp_pos _).le)
        Erdos67b.EulerQuantitative.primeQuadraticConstant_nonneg)
      (mul_nonneg (by norm_num) hshift0)
  have hD0 : 0 ≤ D := (Real.exp_pos _).le
  have hDsq : D ^ 2 = Real.exp q := by
    dsimp only [D]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have htarget : ‖Alt * LSeries (gsA9High g y) sHigh‖ ^ 2 ≤
      (C * B * D) ^ 2 := by
    calc
      _ ≤ C * (B * Real.exp q) * B := hsq'
      _ = C * B ^ 2 * D ^ 2 := by rw [hDsq]; ring
      _ ≤ (C * B * D) ^ 2 := by
        have hnonneg : 0 ≤ (B * D) ^ 2 := sq_nonneg _
        nlinarith
  exact (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (mul_nonneg hC0 hB0) hD0)).mp htarget

/-- Pointwise-distance form of the restored widened Halász estimate for the
original coefficient.  The small Euler factors are restored exactly once. -/
theorem norm_twoBlock_alternatingLow_mul_high_le_wideHalaszPoint_of_distance
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y : ℕ} (hy : 23 ≤ y)
    (hsmallOutside : ∀ p ∈ gsA9SmallPrimeFinset, P₁ p)
    {A X : ℕ} (hX : 1 < X) {sigmaLow t : ℝ}
    (hdist : (A : ℝ) ≤
      pretentiousDistSq f (archimedeanTwist t) X)
    (hhalf : 1 / 2 ≤ sigmaLow)
    (hle : sigmaLow ≤ Erdos67b.EulerResidue.taoExponent X)
    (hsigmaLow : 1 - 3 / Real.log (y : ℝ) ≤ sigmaLow)
    (hgap : Erdos67b.EulerResidue.taoExponent X - sigmaLow ≤
      3 / Real.log (y : ℝ)) :
    let sLow : ℂ := (sigmaLow : ℂ) + Complex.I * (t : ℂ)
    let sHigh : ℂ := Erdos67b.MRHalaszEuler.halaszPoint X t
    ‖LSeries (gsA10TwoBlockAlternatingLow f P₁ P₂ y) sLow *
        LSeries (gsA9High f y) sHigh‖ ≤
      gsA9SmallPrimeEulerBound *
        (gsA9WideSourceEulerConstant * (1 + Real.log (X : ℝ)) *
          Real.exp
            ((-Real.exp (-1) * ((A / 2 : ℕ) : ℝ) +
              3 * Erdos67b.EulerQuantitative.primeQuadraticConstant) / 2)) := by
  dsimp only
  let g : ℕ → ℂ := gsDeletePrimeBand f gsA9SmallPrime
  let sLow : ℂ := (sigmaLow : ℂ) + Complex.I * (t : ℂ)
  let sHigh : ℂ := Erdos67b.MRHalaszEuler.halaszPoint X t
  let Q₂ : ℕ → Prop := fun p ↦ ¬ P₁ p ∧ P₂ p
  let Q₃ : ℕ → Prop := fun p ↦ ¬ P₁ p ∧ ¬ P₂ p
  have hsLow : 0 < sLow.re := by
    simpa only [sLow, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul,
      sub_zero, add_zero] using
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hhalf)
  have hrestore :=
    LSeries_twoBlockAlternatingLow_eq_smallPrime_mul_delete
      hmul hbound P₁ P₂ hy hsmallOutside hsLow
  have hhigh : gsA9High g y = gsA9High f y := by
    exact gsA9High_deleteSmallPrimes_eq f hy
  have hdisj : ∀ p ∈ primesUpTo y, Q₂ p → Q₃ p → False := by
    intro p hp h2 h3
    exact h3.2 h2.2
  have hwide :=
    norm_twoBlock_alternatingLow_deleteSmallPrimes_mul_high_le_wideHalaszPoint_of_distance
      hmul hbound Q₂ Q₃ hy hdisj hX hdist hhalf hle hsigmaLow hgap
  have hmulG : IsMultiplicativeOnPositiveNat g :=
    gsDeletePrimeBand_isMultiplicativeOnPositiveNat hmul gsA9SmallPrime
  have hboundG : ∀ n, 0 < n → ‖g n‖ ≤ 1 := by
    intro n hn
    exact norm_gsDeletePrimeBand_le_one hbound gsA9SmallPrime hn
  have hAltEq := LSeries_gsA10TwoBlockAlternatingLow_of_pos_re
    hmulG hboundG P₁ P₂ y hsLow
  have hwide' :
      ‖LSeries (gsA10TwoBlockAlternatingLow g P₁ P₂ y) sLow *
          LSeries (gsA9High g y) sHigh‖ ≤
        gsA9WideSourceEulerConstant * (1 + Real.log (X : ℝ)) *
          Real.exp
            ((-Real.exp (-1) * ((A / 2 : ℕ) : ℝ) +
              3 * Erdos67b.EulerQuantitative.primeQuadraticConstant) / 2) := by
    rw [hAltEq]
    simpa only [g, sLow, sHigh, Q₂, Q₃] using hwide
  have hsmall : ‖gsA9SmallPrimeEulerProduct f sLow‖ ≤
      gsA9SmallPrimeEulerBound := by
    simpa only [sLow] using
      (norm_gsA9SmallPrimeEulerProduct_le hbound (t := t) hhalf)
  have hsmall0 : 0 ≤ gsA9SmallPrimeEulerBound :=
    (norm_nonneg _).trans hsmall
  have htarget :
      ‖LSeries (gsA10TwoBlockAlternatingLow f P₁ P₂ y) sLow *
          LSeries (gsA9High f y) sHigh‖ ≤
        gsA9SmallPrimeEulerBound *
          (gsA9WideSourceEulerConstant * (1 + Real.log (X : ℝ)) *
            Real.exp
              ((-Real.exp (-1) * ((A / 2 : ℕ) : ℝ) +
                3 * Erdos67b.EulerQuantitative.primeQuadraticConstant) / 2)) := by
    rw [hrestore, ← hhigh]
    rw [show gsA9SmallPrimeEulerProduct f sLow *
        LSeries (gsA10TwoBlockAlternatingLow g P₁ P₂ y) sLow *
          LSeries (gsA9High g y) sHigh =
        gsA9SmallPrimeEulerProduct f sLow *
          (LSeries (gsA10TwoBlockAlternatingLow g P₁ P₂ y) sLow *
            LSeries (gsA9High g y) sHigh) by ring]
    rw [norm_mul]
    exact mul_le_mul hsmall hwide' (norm_nonneg _) hsmall0
  simpa only [sLow, sHigh] using htarget

end

end Erdos67b.MRHalaszBands

#print axioms
  Erdos67b.MRHalaszBands.norm_LSeries_halaszPoint_le_one_add_log_mul_exp_of_distance
#print axioms
  Erdos67b.MRHalaszBands.norm_twoBlock_alternatingLow_deleteSmallPrimes_mul_high_le_wideHalaszPoint_of_distance
#print axioms
  Erdos67b.MRHalaszBands.norm_twoBlock_alternatingLow_mul_high_le_wideHalaszPoint_of_distance
