import ErdosProblems.Erdos67b.MRGSA10SourceMaximumModulus
import ErdosProblems.Erdos67b.MRGSA9SourceHalaszPointWideLocal

/-!
# Source maximum modulus from a local height distance hypothesis

The source rectangle only needs pretentious separation on its actual
vertical range.  This module records that local-height form, retaining the
same source maximum-modulus scalar as the global `MRArch` wrapper.
-/

open scoped LSeries.notation
open Complex Set

namespace Erdos67b.MRHalaszBands

noncomputable section

private theorem norm_LSeries_sourceDeleted_le_one_add_log_localHeight
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {X : ℕ} (hX : 1 < X) {sigma t : ℝ}
    (hsigma : Erdos67b.EulerResidue.taoExponent X ≤ sigma) :
    ‖LSeries (gsA10SourceDeleted f)
        ((sigma : ℂ) + Complex.I * (t : ℂ))‖ ≤
      1 + Real.log (X : ℝ) := by
  let g : ℕ → ℂ := gsA10SourceDeleted f
  have hboundG : ∀ n, 0 < n → ‖g n‖ ≤ 1 := by
    intro n hn
    exact norm_gsDeletePrimeBand_le_one hbound gsA9SmallPrime hn
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast hX)
  have hdelta : (Real.log (X : ℝ))⁻¹ ≤ sigma - 1 := by
    dsimp only [Erdos67b.EulerResidue.taoExponent] at hsigma
    linarith
  have hsigmaOne : 1 < sigma := by
    have hi : 0 < (Real.log (X : ℝ))⁻¹ := inv_pos.mpr hlogX
    linarith
  have hL := Erdos67b.norm_LSeries_le_norm_riemannZeta_real_of_bounded
    hboundG (sigma := sigma) (t := t) hsigmaOne
  have hZ := Erdos67b.norm_riemannZeta_real_le_one_add_inv
    (sigma := sigma - 1) (by linarith : 0 < sigma - 1)
  have hinv : (sigma - 1)⁻¹ ≤ Real.log (X : ℝ) := by
    have := inv_anti₀ (inv_pos.mpr hlogX) hdelta
    simpa only [inv_inv] using this
  calc
    ‖LSeries g ((sigma : ℂ) + Complex.I * (t : ℂ))‖ ≤
        ‖riemannZeta (sigma : ℂ)‖ := hL
    _ ≤ 1 + (sigma - 1)⁻¹ := by
      have hs : 1 + (sigma - 1) = sigma := by ring
      simpa only [hs] using hZ
    _ ≤ 1 + Real.log (X : ℝ) := add_le_add_right hinv 1

private theorem norm_LSeries_sourceDeleted_at_remoteRight_le_two_localHeight
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {X : ℕ} (hX : 1 < X) (t : ℝ) :
    ‖LSeries (gsA10SourceDeleted f)
        ((((2 + Real.log (X : ℝ)) : ℝ) : ℂ) +
          Complex.I * (t : ℂ))‖ ≤ 2 := by
  let g : ℕ → ℂ := gsA10SourceDeleted f
  have hboundG : ∀ n, 0 < n → ‖g n‖ ≤ 1 := by
    intro n hn
    exact norm_gsDeletePrimeBand_le_one hbound gsA9SmallPrime hn
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast hX)
  let sigma : ℝ := 2 + Real.log (X : ℝ)
  have hsigma : 1 < sigma := by dsimp only [sigma]; linarith
  have hL := Erdos67b.norm_LSeries_le_norm_riemannZeta_real_of_bounded
    hboundG (sigma := sigma) (t := t) hsigma
  have hZ := Erdos67b.norm_riemannZeta_real_le_one_add_inv
    (sigma := sigma - 1) (by linarith : 0 < sigma - 1)
  have hinv : (sigma - 1)⁻¹ ≤ 1 := by
    apply (inv_le_one₀ (by linarith : 0 < sigma - 1)).2
    dsimp only [sigma]
    linarith
  calc
    ‖LSeries g ((sigma : ℂ) + Complex.I * (t : ℂ))‖ ≤
        ‖riemannZeta (sigma : ℂ)‖ := hL
    _ ≤ 1 + (sigma - 1)⁻¹ := by
      have hs : 1 + (sigma - 1) = sigma := by ring
      simpa only [hs] using hZ
    _ ≤ 2 := by linarith

/-- Maximum-modulus estimate on a rectangle of height `T`.  The
pretentious-distance lower bound is required only on that rectangle. -/
theorem norm_sourceDeleted_LSeries_div_sq_le_maximumModulusScalar_of_localHeight
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {A X : ℕ} (hX : 1 < X)
    (hlogX : 1 ≤ Real.log (X : ℝ))
    {T : ℝ} (hT0 : 0 < T)
    (hlogT : 1 + Real.log (X : ℝ) ≤ T ^ 2)
    (hdist : ∀ u : ℝ, |u| ≤ T →
      (A : ℝ) ≤ pretentiousDistSq f (archimedeanTwist u) X)
    {beta t : ℝ} (hbeta0 : 0 ≤ beta) (hbeta : beta ≤ 1 / 4)
    (ht : |t| ≤ T) :
    let c₀ := Erdos67b.EulerResidue.taoExponent X
    let s : ℂ := ((c₀ + beta : ℝ) : ℂ) + Complex.I * (t : ℂ)
    ‖LSeries (gsA10SourceDeleted f) s / s ^ 2‖ ≤
      gsA10SourceMaximumModulusScalar A X := by
  dsimp only
  let g : ℕ → ℂ := gsA10SourceDeleted f
  let c₀ : ℝ := Erdos67b.EulerResidue.taoExponent X
  let b : ℝ := 2 + Real.log (X : ℝ)
  let C : ℝ := gsA10SourceMaximumModulusScalar A X
  let F : ℂ → ℂ := fun z ↦ LSeries g z / z ^ 2
  have hboundG : ∀ n, 0 < n → ‖g n‖ ≤ 1 := by
    intro n hn
    exact norm_gsDeletePrimeBand_le_one hbound gsA9SmallPrime hn
  have hboundG' : ∀ n, n ≠ 0 → ‖g n‖ ≤ 1 := by
    intro n hn
    exact hboundG n (Nat.pos_of_ne_zero hn)
  have hlogXpos : 0 < Real.log (X : ℝ) := zero_lt_one.trans_le hlogX
  have hcStrict : 1 < c₀ := by
    dsimp only [c₀]
    exact Erdos67b.EulerResidue.one_lt_taoExponent hX
  have hcb : c₀ < b := by
    dsimp only [c₀, b, Erdos67b.EulerResidue.taoExponent]
    have hinv : (Real.log (X : ℝ))⁻¹ ≤ 1 :=
      (inv_le_one₀ hlogXpos).2 hlogX
    linarith
  have hvertical : -T < T := by linarith
  have hFdiff : DiffContOnCl ℂ F (Ioo c₀ b ×ℂ Ioo (-T) T) := by
    have hmid : 1 < (c₀ + 1) / 2 := by linarith
    have hsum : LSeriesSummable g (((c₀ + 1) / 2 : ℝ) : ℂ) :=
      LSeriesSummable_of_bounded_of_one_lt_re hboundG' (by simpa using hmid)
    have habs : LSeries.abscissaOfAbsConv g < (c₀ : EReal) := by
      calc
        LSeries.abscissaOfAbsConv g ≤ (((c₀ + 1) / 2 : ℝ) : EReal) := by
          simpa using hsum.abscissaOfAbsConv_le
        _ < (c₀ : ℝ) := by
          exact_mod_cast (by linarith : (c₀ + 1) / 2 < c₀)
    apply DifferentiableOn.diffContOnCl
    rw [closure_reProdIm, closure_Ioo hcb.ne, closure_Ioo hvertical.ne]
    intro z hz
    have hz0 : z ≠ 0 := by
      intro hzero
      have hzre : 1 < z.re := hcStrict.trans_le hz.1.1
      rw [hzero] at hzre
      norm_num at hzre
    have hLz : DifferentiableAt ℂ (LSeries g) z := by
      have hzr : (c₀ : EReal) ≤ (z.re : EReal) := by
        exact_mod_cast hz.1.1
      exact (LSeries_hasDerivAt (habs.trans_le hzr)).differentiableAt
    have hid : DifferentiableAt ℂ (fun w : ℂ ↦ w) z := differentiableAt_id
    exact (hLz.div (hid.pow 2) (pow_ne_zero 2 hz0)).differentiableWithinAt
  have hC0 : 0 ≤ C := by
    unfold C gsA10SourceMaximumModulusScalar
    positivity
  have hleft : ∀ y ∈ Icc (-T) T,
      ‖F ((c₀ : ℂ) + Complex.I * y)‖ ≤ C := by
    intro y hy
    have hyAbs : |y| ≤ T := abs_le.mpr ⟨hy.1, hy.2⟩
    have hdistY := hdist y hyAbs
    have hdistG : (((A / 2 : ℕ) : ℝ)) ≤
        pretentiousDistSq g (archimedeanTwist y) X := by
      calc
        ((A / 2 : ℕ) : ℝ) ≤ (A : ℝ) / 2 := by
          simpa only [Nat.cast_ofNat] using (Nat.cast_div_le :
            ((A / 2 : ℕ) : ℝ) ≤ (A : ℝ) / (2 : ℝ))
        _ ≤ pretentiousDistSq g (archimedeanTwist y) X := by
          refine (div_le_div_of_nonneg_right hdistY (by norm_num)).trans ?_
          exact half_pretentiousDistSq_le_deletePrimeBand
            (fun p hp ↦ hbound p hp.pos)
            (fun p hp ↦ by rw [norm_archimedeanTwist hp.pos])
            gsA9SmallPrime X
    have hL := norm_LSeries_halaszPoint_le_one_add_log_mul_exp_of_distance
      (gsDeletePrimeBand_isMultiplicativeOnPositiveNat hmul gsA9SmallPrime)
      hboundG hX hdistG
    have hsNorm : 1 ≤ ‖(c₀ : ℂ) + Complex.I * (y : ℂ)‖ := by
      have hre := Complex.abs_re_le_norm ((c₀ : ℂ) + Complex.I * (y : ℂ))
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul,
        sub_zero] at hre
      rw [add_zero, abs_of_pos (by linarith : 0 < c₀)] at hre
      exact (le_of_lt hcStrict).trans hre
    have hden : 1 ≤ ‖((c₀ : ℂ) + Complex.I * (y : ℂ)) ^ 2‖ := by
      rw [Complex.norm_pow]
      nlinarith [norm_nonneg ((c₀ : ℂ) + Complex.I * (y : ℂ))]
    unfold F
    rw [norm_div]
    calc
      ‖LSeries g ((c₀ : ℂ) + Complex.I * (y : ℂ))‖ /
            ‖((c₀ : ℂ) + Complex.I * (y : ℂ)) ^ 2‖ ≤
          ‖LSeries g ((c₀ : ℂ) + Complex.I * (y : ℂ))‖ := by
        exact div_le_self (norm_nonneg _) hden
      _ ≤ (1 + Real.log (X : ℝ)) *
          Real.exp
            (-Real.exp (-1) * ((A / 2 : ℕ) : ℝ) +
              3 * Erdos67b.EulerQuantitative.primeQuadraticConstant) := by
        simpa only [g, gsA10SourceDeleted, c₀,
          Erdos67b.MRHalaszEuler.halaszPoint] using hL
      _ ≤ C := by unfold C gsA10SourceMaximumModulusScalar; linarith
  have hright : ∀ y ∈ Icc (-T) T,
      ‖F ((b : ℂ) + Complex.I * y)‖ ≤ C := by
    intro y hy
    have hL := norm_LSeries_sourceDeleted_at_remoteRight_le_two_localHeight
      hbound hX y
    have hsNorm : 2 ≤ ‖(b : ℂ) + Complex.I * (y : ℂ)‖ := by
      have hre := Complex.abs_re_le_norm ((b : ℂ) + Complex.I * (y : ℂ))
      have hbTwo : 2 ≤ b := by dsimp only [b]; linarith
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul,
        sub_zero] at hre
      rw [add_zero, abs_of_nonneg (by linarith : 0 ≤ b)] at hre
      exact hbTwo.trans hre
    have hden : 4 ≤ ‖((b : ℂ) + Complex.I * (y : ℂ)) ^ 2‖ := by
      rw [Complex.norm_pow]
      nlinarith [norm_nonneg ((b : ℂ) + Complex.I * (y : ℂ))]
    have hC1 : 1 ≤ C := by
      unfold C gsA10SourceMaximumModulusScalar
      have hmain : 0 ≤ (1 + Real.log (X : ℝ)) *
          Real.exp
            (-Real.exp (-1) * ((A / 2 : ℕ) : ℝ) +
              3 * Erdos67b.EulerQuantitative.primeQuadraticConstant) := by
        positivity
      linarith
    unfold F
    rw [norm_div]
    calc
      ‖LSeries g ((b : ℂ) + Complex.I * (y : ℂ))‖ /
          ‖((b : ℂ) + Complex.I * (y : ℂ)) ^ 2‖ ≤ 1 := by
        apply (div_le_iff₀ (by linarith : 0 <
          ‖((b : ℂ) + Complex.I * (y : ℂ)) ^ 2‖)).2
        calc
          ‖LSeries g ((b : ℂ) + Complex.I * (y : ℂ))‖ ≤ 2 := by
            simpa only [g, b] using hL
          _ ≤ ‖((b : ℂ) + Complex.I * (y : ℂ)) ^ 2‖ := by linarith
          _ = 1 * ‖((b : ℂ) + Complex.I * (y : ℂ)) ^ 2‖ := by ring
      _ ≤ C := hC1
  have hhorizontal : ∀ x ∈ Icc c₀ b, ∀ u : ℝ, |u| = T →
      ‖F ((x : ℂ) + Complex.I * u)‖ ≤ C := by
    intro x hx u hu
    have hL := norm_LSeries_sourceDeleted_le_one_add_log_localHeight
      hbound hX (sigma := x) (t := u) hx.1
    have hsNorm : T ≤ ‖(x : ℂ) + Complex.I * (u : ℂ)‖ := by
      have him := Complex.abs_im_le_norm ((x : ℂ) + Complex.I * (u : ℂ))
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, zero_mul, zero_add,
        one_mul] at him
      rw [hu] at him
      exact him
    have hden : T ^ 2 ≤ ‖((x : ℂ) + Complex.I * (u : ℂ)) ^ 2‖ := by
      rw [Complex.norm_pow]
      nlinarith [norm_nonneg ((x : ℂ) + Complex.I * (u : ℂ))]
    have hC1 : 1 ≤ C := by
      unfold C gsA10SourceMaximumModulusScalar
      have hmain : 0 ≤ (1 + Real.log (X : ℝ)) *
          Real.exp
            (-Real.exp (-1) * ((A / 2 : ℕ) : ℝ) +
              3 * Erdos67b.EulerQuantitative.primeQuadraticConstant) := by
        positivity
      linarith
    unfold F
    rw [norm_div]
    calc
      ‖LSeries g ((x : ℂ) + Complex.I * (u : ℂ))‖ /
          ‖((x : ℂ) + Complex.I * (u : ℂ)) ^ 2‖ ≤ 1 := by
        apply (div_le_iff₀ (by
          nlinarith [sq_pos_of_pos hT0] : 0 <
            ‖((x : ℂ) + Complex.I * (u : ℂ)) ^ 2‖)).2
        calc
          ‖LSeries g ((x : ℂ) + Complex.I * (u : ℂ))‖ ≤
              1 + Real.log (X : ℝ) := by simpa only [g] using hL
          _ ≤ T ^ 2 := hlogT
          _ ≤ ‖((x : ℂ) + Complex.I * (u : ℂ)) ^ 2‖ := hden
          _ = 1 * ‖((x : ℂ) + Complex.I * (u : ℂ)) ^ 2‖ := by ring
      _ ≤ C := hC1
  have hbottom : ∀ x ∈ Icc c₀ b,
      ‖F ((x : ℂ) + Complex.I * (-T))‖ ≤ C := by
    intro x hx
    simpa only [Complex.ofReal_neg] using
      (hhorizontal x hx (-T) (by simp [abs_of_pos hT0]))
  have htop : ∀ x ∈ Icc c₀ b,
      ‖F ((x : ℂ) + Complex.I * T)‖ ≤ C := by
    intro x hx
    exact hhorizontal x hx T (by simp [abs_of_pos hT0])
  let s : ℂ := ((c₀ + beta : ℝ) : ℂ) + Complex.I * (t : ℂ)
  have hsre : s.re ∈ Icc c₀ b := by
    have hbTarget : c₀ + beta ≤ b := by
      have hcTwo : c₀ ≤ 2 := by
        dsimp only [c₀, Erdos67b.EulerResidue.taoExponent]
        have hinv : (Real.log (X : ℝ))⁻¹ ≤ 1 :=
          (inv_le_one₀ hlogXpos).2 hlogX
        linarith
      dsimp only [b]
      linarith
    dsimp only [s]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul,
      sub_zero, add_zero]
    exact ⟨by linarith, hbTarget⟩
  have hsim : s.im ∈ Icc (-T) T := by
    dsimp only [s]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, zero_mul, zero_add,
      one_mul]
    exact abs_le.mp ht
  have hmax := Erdos67b.norm_le_on_closedRectangle_of_four_sides
    hcb hvertical hFdiff hleft hright
      (fun x hx ↦ by simpa only [Complex.ofReal_neg] using hbottom x hx)
      htop hsre hsim
  simpa only [F, g, s, c₀, C] using hmax

/-- Square-root form of the local-height maximum-modulus estimate. -/
theorem sqrt_norm_sourceDeleted_LSeries_div_norm_le_maximumModulusSqrtScalar_of_localHeight
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {A X : ℕ} (hX : 1 < X)
    (hlogX : 1 ≤ Real.log (X : ℝ))
    {T : ℝ} (hT0 : 0 < T)
    (hlogT : 1 + Real.log (X : ℝ) ≤ T ^ 2)
    (hdist : ∀ u : ℝ, |u| ≤ T →
      (A : ℝ) ≤ pretentiousDistSq f (archimedeanTwist u) X)
    {beta t : ℝ} (hbeta0 : 0 ≤ beta) (hbeta : beta ≤ 1 / 4)
    (ht : |t| ≤ T) :
    let c₀ := Erdos67b.EulerResidue.taoExponent X
    let s : ℂ := ((c₀ + beta : ℝ) : ℂ) + Complex.I * (t : ℂ)
    Real.sqrt ‖LSeries (gsA10SourceDeleted f) s‖ / ‖s‖ ≤
      gsA10SourceMaximumModulusSqrtScalar A X := by
  dsimp only
  let c₀ : ℝ := Erdos67b.EulerResidue.taoExponent X
  let s : ℂ := ((c₀ + beta : ℝ) : ℂ) + Complex.I * (t : ℂ)
  let q : ℝ := -Real.exp (-1) * ((A / 2 : ℕ) : ℝ) +
    3 * Erdos67b.EulerQuantitative.primeQuadraticConstant
  let a : ℝ := Real.sqrt (1 + Real.log (X : ℝ)) * Real.exp (q / 2)
  let R : ℝ := Real.sqrt ‖LSeries (gsA10SourceDeleted f) s‖ / ‖s‖
  let B : ℝ := gsA10SourceMaximumModulusSqrtScalar A X
  have hmax :=
    norm_sourceDeleted_LSeries_div_sq_le_maximumModulusScalar_of_localHeight
      hmul hbound hX hlogX hT0 hlogT hdist hbeta0 hbeta ht
  have hlog0 : 0 ≤ 1 + Real.log (X : ℝ) := by linarith
  have ha0 : 0 ≤ a := by dsimp only [a]; positivity
  have hB : B = a + 1 := by
    dsimp only [B, a, q, gsA10SourceMaximumModulusSqrtScalar]
  have hC : gsA10SourceMaximumModulusScalar A X = a ^ 2 + 1 := by
    dsimp only [a, q, gsA10SourceMaximumModulusScalar]
    rw [mul_pow, Real.sq_sqrt hlog0, pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsRe : 0 < s.re := by
    dsimp only [s, c₀]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul,
      sub_zero, add_zero]
    have hc := Erdos67b.EulerResidue.one_lt_taoExponent hX
    linarith
  have hsNorm : 0 < ‖s‖ := by
    exact (abs_pos.mpr (ne_of_gt hsRe)).trans_le
      (Complex.abs_re_le_norm s)
  have hRsq : R ^ 2 =
      ‖LSeries (gsA10SourceDeleted f) s / s ^ 2‖ := by
    dsimp only [R]
    rw [div_pow, Real.sq_sqrt (norm_nonneg _), norm_div,
      Complex.norm_pow]
  have hB0 : 0 ≤ B := by rw [hB]; linarith
  have htarget : R ^ 2 ≤ B ^ 2 := by
    rw [hRsq]
    calc
      ‖LSeries (gsA10SourceDeleted f) s / s ^ 2‖ ≤
          gsA10SourceMaximumModulusScalar A X := by
        simpa only [c₀, s] using hmax
      _ = a ^ 2 + 1 := hC
      _ ≤ (a + 1) ^ 2 := by nlinarith
      _ = B ^ 2 := by rw [hB]
  have hR0 : 0 ≤ R := div_nonneg (Real.sqrt_nonneg _) hsNorm.le
  exact (sq_le_sq₀ hR0 hB0).mp htarget

/-- The source Perron envelope controlled from pretentious separation only
on the actual vertical integration window. -/
theorem gsA10SourcePerronEnvelope_le_maximumModulus_of_localHeight
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {A X : ℕ} (hX : 1 < X)
    (hlogX : 1 ≤ Real.log (X : ℝ))
    {T : ℝ} (hT0 : 0 < T)
    (hlogT : 1 + Real.log (X : ℝ) ≤ T ^ 2)
    (hdist : ∀ u : ℝ, |u| ≤ T →
      (A : ℝ) ≤ pretentiousDistSq f (archimedeanTwist u) X)
    {beta t : ℝ} (hbeta0 : 0 ≤ beta) (hbeta : beta ≤ 1 / 4)
    (ht : |t| ≤ T) :
    gsA10SourcePerronEnvelope f X beta t ≤
      Real.exp
          (28 * Real.exp 4 *
              Erdos67b.EulerQuantitative.primeQuadraticConstant +
            36 * gsA9SourceShiftConstant) *
        gsA10SourceMaximumModulusSqrtScalar A X *
        Real.sqrt
          ‖riemannZeta
            (((Erdos67b.EulerResidue.taoExponent X + beta : ℝ) : ℂ))‖ := by
  let c₀ : ℝ := Erdos67b.EulerResidue.taoExponent X
  let s : ℂ := ((c₀ + beta : ℝ) : ℂ) + Complex.I * (t : ℂ)
  let K : ℝ := Real.exp
    (28 * Real.exp 4 *
        Erdos67b.EulerQuantitative.primeQuadraticConstant +
      36 * gsA9SourceShiftConstant)
  have hsqrt :=
    sqrt_norm_sourceDeleted_LSeries_div_norm_le_maximumModulusSqrtScalar_of_localHeight
      hmul hbound hX hlogX hT0 hlogT hdist hbeta0 hbeta ht
  have hK0 : 0 ≤ K := (Real.exp_pos _).le
  have hz0 : 0 ≤ Real.sqrt ‖riemannZeta ((c₀ + beta : ℝ) : ℂ)‖ :=
    Real.sqrt_nonneg _
  unfold gsA10SourcePerronEnvelope gsA10SourceWindowCoreBudget
  dsimp only
  change K * Real.sqrt ‖LSeries (gsA10SourceDeleted f) s‖ *
      Real.sqrt ‖riemannZeta ((c₀ + beta : ℝ) : ℂ)‖ / ‖s‖ ≤ _
  have hmul' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (by simpa only [c₀, s] using hsqrt) hK0) hz0
  calc
    K * Real.sqrt ‖LSeries (gsA10SourceDeleted f) s‖ *
        Real.sqrt ‖riemannZeta ((c₀ + beta : ℝ) : ℂ)‖ / ‖s‖ =
      (K * (Real.sqrt ‖LSeries (gsA10SourceDeleted f) s‖ / ‖s‖)) *
        Real.sqrt ‖riemannZeta ((c₀ + beta : ℝ) : ℂ)‖ := by ring
    _ ≤ (K * gsA10SourceMaximumModulusSqrtScalar A X) *
        Real.sqrt ‖riemannZeta ((c₀ + beta : ℝ) : ℂ)‖ := hmul'
    _ = _ := by simp only [K, c₀]

end

end Erdos67b.MRHalaszBands

#print axioms
  Erdos67b.MRHalaszBands.norm_sourceDeleted_LSeries_div_sq_le_maximumModulusScalar_of_localHeight
#print axioms
  Erdos67b.MRHalaszBands.gsA10SourcePerronEnvelope_le_maximumModulus_of_localHeight
