import Arxiv.Arxiv2407_19026.TangentAssembly
import Arxiv.Arxiv2407_19026.TangentPolynomialBounds

/-!
# Kernel-checked tangent bounds

Elementary analytic estimates used to replace executable affine-cover
certificates with compact proofs checked entirely by the Lean kernel.
-/

namespace Arxiv2407_19026

noncomputable section

private def smallExpFactor (β z : ℝ) : ℝ :=
  Real.exp (-Real.log (1 + z) - tangentCorrectionSlope β z)

private def smallExpLower (z : ℝ) : ℝ := 5 / 4 - 2 * z

private def smallPrimeLower (z : ℝ) : ℝ :=
  smallExpLower z * (1 - 7 / 4 * z)

private def smallPUpper (z : ℝ) : ℝ :=
  1 - z * smallExpLower z

private def smallOmUpper (z : ℝ) : ℝ :=
  1 - z * (1 - z)

private lemma exp_neg_bounds {z : ℝ} (hz : z ∈ Set.Icc 0 (1 / 10)) :
    1 - z ≤ Real.exp (-z) ∧ Real.exp (-z) ≤ 1 := by
  constructor
  · linarith [Real.add_one_le_exp (-z)]
  · exact Real.exp_le_one_iff.mpr (by linarith [hz.1])

private lemma correction_slope_upper {β z : ℝ}
    (hβ : β ∈ Set.Icc 0 (2 / 25))
    (hz : z ∈ Set.Icc 0 (1 / 10)) :
    tangentCorrectionSlope β z ≤ -1 / 4 + z := by
  have he := (exp_neg_bounds hz).1
  let C : ℝ :=
    -(1 / 4) + 2 * β * z + 6 / 25 * z ^ 2 -
      (-(1 / 4) * z + β * z ^ 2 + 2 / 25 * z ^ 3)
  have hC : C ≤ 0 := by
    dsimp [C]
    have hz2 : z ^ 2 ≤ 1 / 100 := by
      nlinarith [mul_nonneg hz.1 (sub_nonneg.mpr hz.2)]
    have hz3 : z ^ 3 ≤ 1 / 1000 := by
      nlinarith [mul_nonneg (sq_nonneg z) (sub_nonneg.mpr hz.2)]
    have hβz : β * z ≤ (2 / 25 : ℝ) * (1 / 10) :=
      mul_le_mul hβ.2 hz.2 hz.1 (by norm_num)
    nlinarith [mul_nonneg hβ.1 (sq_nonneg z),
      mul_nonneg (sq_nonneg z) hz.1]
  have hmul : C * Real.exp (-z) ≤ C * (1 - z) :=
    mul_le_mul_of_nonpos_left he hC
  have hpoly : C * (1 - z) ≤ -1 / 4 + z := by
    dsimp [C]
    have hz2 : z ^ 2 ≤ 1 / 100 := by
      nlinarith [mul_nonneg hz.1 (sub_nonneg.mpr hz.2)]
    have hz3 : z ^ 3 ≤ 1 / 1000 := by
      nlinarith [mul_nonneg (sq_nonneg z) (sub_nonneg.mpr hz.2)]
    have hz4 : z ^ 4 ≤ 1 / 10000 := by
      nlinarith [mul_nonneg (mul_nonneg hz.1 (sq_nonneg z))
        (sub_nonneg.mpr hz.2)]
    have hβz : β * z ≤ (2 / 25 : ℝ) * (1 / 10) :=
      mul_le_mul hβ.2 hz.2 hz.1 (by norm_num)
    have hβz2 : β * z ^ 2 ≤ (2 / 25 : ℝ) * (1 / 100) :=
      mul_le_mul hβ.2 hz2 (sq_nonneg z) (by norm_num)
    have hβz3 : β * z ^ 3 ≤ (2 / 25 : ℝ) * (1 / 1000) :=
      mul_le_mul hβ.2 hz3 (by
        exact mul_nonneg (sq_nonneg z) hz.1) (by norm_num)
    let B : ℝ :=
      50 + z + 32 * z ^ 2 - 8 * z ^ 3 -
        200 * β + 300 * β * z - 100 * β * z ^ 2
    have hB : 0 ≤ B := by
      dsimp [B]
      have hb : 200 * β ≤ 16 := by nlinarith [hβ.2]
      have hbz2 : 100 * β * z ^ 2 ≤ 2 / 25 := by
        nlinarith [hβz2]
      have hz3' : 8 * z ^ 3 ≤ 1 / 125 := by
        nlinarith [hz3]
      nlinarith [mul_nonneg hz.1 (sq_nonneg z),
        mul_nonneg hβ.1 hz.1]
    have hid :
        (-1 / 4 + z) - C * (1 - z) = z * B / 100 := by
      dsimp [B, C]
      ring
    rw [← sub_nonneg, hid]
    exact div_nonneg (mul_nonneg hz.1 hB) (by norm_num)
  change C * Real.exp (-z) ≤ -1 / 4 + z
  exact hmul.trans hpoly

private lemma correction_slope_deriv_upper {β z : ℝ}
    (hβ : β ∈ Set.Icc 0 (2 / 25))
    (hz : z ∈ Set.Icc 0 (1 / 10)) :
    tangentCorrectionSlopeDeriv β z ≤ 3 / 4 := by
  let D : ℝ :=
    (2 * β + 12 / 25 * z -
        (-(1 / 4) + 2 * β * z + 6 / 25 * z ^ 2)) -
      (-(1 / 4) + 2 * β * z + 6 / 25 * z ^ 2 -
        (-(1 / 4) * z + β * z ^ 2 + 2 / 25 * z ^ 3))
  have hD0 : 0 ≤ D := by
    have hDid :
        D = 1 / 2 + 2 * β - 4 * β * z + β * z ^ 2 +
          23 / 100 * z - 12 / 25 * z ^ 2 + 2 / 25 * z ^ 3 := by
      dsimp [D]
      ring
    have hz2 : z ^ 2 ≤ 1 / 100 := by
      nlinarith [mul_nonneg hz.1 (sub_nonneg.mpr hz.2)]
    have hz3 : z ^ 3 ≤ 1 / 1000 := by
      nlinarith [mul_nonneg (sq_nonneg z) (sub_nonneg.mpr hz.2)]
    have hβz : β * z ≤ (2 / 25 : ℝ) * (1 / 10) :=
      mul_le_mul hβ.2 hz.2 hz.1 (by norm_num)
    have hβz0 : 0 ≤ β * z := mul_nonneg hβ.1 hz.1
    have hβz20 : 0 ≤ β * z ^ 2 :=
      mul_nonneg hβ.1 (sq_nonneg z)
    have hz30 : 0 ≤ z ^ 3 := mul_nonneg (sq_nonneg z) hz.1
    have hbase :
        0 ≤ 1 / 2 - 4 * β * z - 12 / 25 * z ^ 2 := by
      nlinarith
    have hrest :
        0 ≤ 2 * β + β * z ^ 2 +
          23 / 100 * z + 2 / 25 * z ^ 3 := by
      exact add_nonneg
        (add_nonneg
          (add_nonneg (mul_nonneg (by norm_num) hβ.1) hβz20)
          (mul_nonneg (by norm_num) hz.1))
        (mul_nonneg (by norm_num) hz30)
    rw [hDid]
    linarith
  have hD1 : D ≤ 3 / 4 := by
    have hDid :
        D = 1 / 2 + 2 * β - 4 * β * z + β * z ^ 2 +
          23 / 100 * z - 12 / 25 * z ^ 2 + 2 / 25 * z ^ 3 := by
      dsimp [D]
      ring
    have hz2 : z ^ 2 ≤ 1 / 100 := by
      nlinarith [mul_nonneg hz.1 (sub_nonneg.mpr hz.2)]
    have hz3 : z ^ 3 ≤ 1 / 1000 := by
      nlinarith [mul_nonneg (sq_nonneg z) (sub_nonneg.mpr hz.2)]
    have hβz : β * z ≤ (2 / 25 : ℝ) * (1 / 10) :=
      mul_le_mul hβ.2 hz.2 hz.1 (by norm_num)
    have hβz2 : β * z ^ 2 ≤ (2 / 25 : ℝ) * (1 / 100) :=
      mul_le_mul hβ.2 hz2 (sq_nonneg z) (by norm_num)
    have hβz0 : 0 ≤ β * z := mul_nonneg hβ.1 hz.1
    have hz30 : 0 ≤ z ^ 3 := mul_nonneg (sq_nonneg z) hz.1
    rw [hDid]
    nlinarith [hβ.2, hz.2]
  have he := (exp_neg_bounds hz).2
  have hmul : D * Real.exp (-z) ≤ D :=
    (mul_le_mul_of_nonneg_left he hD0).trans_eq (mul_one D)
  unfold tangentCorrectionSlopeDeriv
  dsimp only
  exact hmul.trans hD1

private lemma small_exp_factor_lower {β z : ℝ}
    (hβ : β ∈ Set.Icc 0 (2 / 25))
    (hz : z ∈ Set.Icc 0 (1 / 10)) :
    smallExpLower z ≤ smallExpFactor β z := by
  have hlog := Real.log_le_sub_one_of_pos (by linarith [hz.1] : 0 < 1 + z)
  have hcorr := correction_slope_upper hβ hz
  have hexp := Real.add_one_le_exp
    (-Real.log (1 + z) - tangentCorrectionSlope β z)
  unfold smallExpLower smallExpFactor
  norm_num at hlog ⊢
  linarith

private lemma small_exp_lower_pos {z : ℝ}
    (hz : z ∈ Set.Icc 0 (1 / 10)) :
    0 < smallExpLower z := by
  unfold smallExpLower
  norm_num at hz ⊢
  linarith

private lemma tangent_blue_lower {β z : ℝ}
    (hβ : β ∈ Set.Icc 0 (2 / 25))
    (hz : z ∈ Set.Icc 0 (1 / 10)) :
    z * smallExpLower z ≤ tangentBlue β z := by
  have he := small_exp_factor_lower hβ hz
  change z * smallExpLower z ≤ z * smallExpFactor β z
  exact mul_le_mul_of_nonneg_left he hz.1

private lemma tangent_mu_bounds {z : ℝ}
    (hz : z ∈ Set.Icc 0 (1 / 10)) :
    (1 - z) ^ 2 ≤ tangentMuPrime z ∧
      z * (1 - z) ≤ optimizationM z := by
  have he := (exp_neg_bounds hz).1
  constructor
  · unfold tangentMuPrime
    have hz1 : 0 ≤ 1 - z := by linarith [hz.2]
    nlinarith [mul_le_mul_of_nonneg_left he hz1]
  · unfold optimizationM
    exact mul_le_mul_of_nonneg_left he hz.1

private lemma tangent_blue_prime_lower {β z : ℝ}
    (hβ : β ∈ Set.Icc 0 (2 / 25))
    (hz : z ∈ Set.Icc 0 (1 / 10)) :
    smallPrimeLower z ≤ tangentBluePrime β z := by
  have he := small_exp_factor_lower hβ hz
  have hd := correction_slope_deriv_upper hβ hz
  have hzplus : 0 < 1 + z := by linarith [hz.1]
  have hinv : (1 + z)⁻¹ ≤ 1 :=
    (inv_le_one₀ hzplus).mpr (by linarith [hz.1])
  let F : ℝ :=
    1 - z * ((1 + z)⁻¹ + tangentCorrectionSlopeDeriv β z)
  have hF : 1 - 7 / 4 * z ≤ F := by
    dsimp [F]
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add hinv hd) hz.1]
  have hF0 : 0 ≤ F := by
    dsimp [F] at hF ⊢
    nlinarith [hz.2]
  have hL0 : 0 ≤ smallExpLower z := (small_exp_lower_pos hz).le
  have hflow : 0 ≤ 1 - 7 / 4 * z := by nlinarith [hz.2]
  have hmul₁ :
      smallExpLower z * (1 - 7 / 4 * z) ≤
        smallExpLower z * F :=
    mul_le_mul_of_nonneg_left hF hL0
  have hmul₂ :
      smallExpLower z * F ≤ smallExpFactor β z * F :=
    mul_le_mul_of_nonneg_right he hF0
  change smallPrimeLower z ≤ smallExpFactor β z * F
  exact hmul₁.trans hmul₂

private lemma tangent_alog_prime_lower {β z : ℝ}
    (hβ : β ∈ Set.Icc 0 (2 / 25))
    (hz : z ∈ Set.Icc 0 (1 / 10)) :
    -(1 + tangentSmallT z)⁻¹ ≤
      tangentALogPrime β (tangentSmallT z) := by
  let t := tangentSmallT z
  let q : ℝ :=
    1 / 4 + β + (4 / 25 - β) * t - 2 / 25 * t ^ 2
  let q' : ℝ := 4 / 25 - β - 4 / 25 * t
  have ht0 : 0 ≤ t := by
    dsimp [t, tangentSmallT]
    nlinarith [hz.1]
  have ht1 : t ≤ 11 / 50 := by
    dsimp [t, tangentSmallT]
    nlinarith [hz.2]
  have hq : 0 ≤ q := by
    have ht2 : t ^ 2 ≤ (11 / 50 : ℝ) ^ 2 := by
      nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht1)]
    have hmid : 0 ≤ (4 / 25 - β) * t :=
      mul_nonneg (sub_nonneg.mpr
        (hβ.2.trans (by norm_num))) ht0
    have hbase : 0 ≤ 1 / 4 - 2 / 25 * t ^ 2 := by
      nlinarith
    have hrest : 0 ≤ β + (4 / 25 - β) * t := by
      exact add_nonneg hβ.1 hmid
    dsimp [q]
    nlinarith
  have hq' : 0 ≤ q' := by
    dsimp [q']
    norm_num at hβ ht1 ⊢
    linarith
  have hR :
      0 ≤ 2 * t * q + t ^ 2 * q' - t ^ 2 * q := by
    have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
    have h2t : 0 ≤ 2 - t := by nlinarith
    have hid :
        2 * t * q + t ^ 2 * q' - t ^ 2 * q =
          t * (2 - t) * q + t ^ 2 * q' := by ring
    rw [hid]
    positivity
  have hprod :
      0 ≤ Real.exp (-t) *
        (2 * t * q + t ^ 2 * q' - t ^ 2 * q) :=
    mul_nonneg (Real.exp_pos _).le hR
  change -(1 + t)⁻¹ ≤
    -(1 + t)⁻¹ +
      Real.exp (-t) *
        (2 * t * q + t ^ 2 * q' - t ^ 2 * q)
  linarith

private lemma small_rational_margin {z : ℝ}
    (hz : z ∈ Set.Icc 0 (1 / 10)) :
    1 / 20 + (11 / 5) / (1 + (11 / 5) * z) ≤
      smallPrimeLower z /
          (smallPUpper z * smallOmUpper z) +
        (1 - z) ^ 2 / smallOmUpper z := by
  have hz2 : z ^ 2 ≤ 1 / 100 := by
    nlinarith [mul_nonneg hz.1 (sub_nonneg.mpr hz.2)]
  have hz3 : z ^ 3 ≤ 1 / 1000 := by
    nlinarith [mul_nonneg (sq_nonneg z) (sub_nonneg.mpr hz.2)]
  have hbracket :
      0 ≤ 1672 * z ^ 4 - 5477 * z ^ 3 + 8558 * z ^ 2 -
        6671 * z + 986 := by
    nlinarith [sq_nonneg (z ^ 2)]
  have hnum :
      0 ≤ z * (1672 * z ^ 4 - 5477 * z ^ 3 +
        8558 * z ^ 2 - 6671 * z + 986) :=
    mul_nonneg hz.1 hbracket
  have hA : 0 < 1 + (11 / 5 : ℝ) * z := by
    nlinarith [hz.1]
  have hP : 0 < smallPUpper z := by
    unfold smallPUpper smallExpLower
    nlinarith [hz2]
  have hO : 0 < smallOmUpper z := by
    unfold smallOmUpper
    nlinarith [hz2]
  have hQ : 0 < 11 * z + 5 := by nlinarith [hz.1]
  have hR : 0 < z ^ 2 - z + 1 := by nlinarith [hz2]
  have hS : 0 < 8 * z ^ 2 - 5 * z + 4 := by nlinarith [hz2, hz.2]
  have hAid :
      1 + (11 / 5 : ℝ) * z = (11 * z + 5) / 5 := by ring
  have hPid :
      smallPUpper z = (8 * z ^ 2 - 5 * z + 4) / 4 := by
    unfold smallPUpper smallExpLower
    ring
  have hOid :
      smallOmUpper z = z ^ 2 - z + 1 := by
    unfold smallOmUpper
    ring
  let A : ℝ := (11 * z + 5) / 5
  let P : ℝ := (8 * z ^ 2 - 5 * z + 4) / 4
  let O : ℝ := z ^ 2 - z + 1
  let B : ℝ := smallPrimeLower z
  let M : ℝ := (1 - z) ^ 2
  have hA' : 0 < A := by dsimp [A]; positivity
  have hP' : 0 < P := by dsimp [P]; positivity
  have hO' : 0 < O := by dsimp [O]; exact hR
  have hlhs :
      1 / 20 + (11 / 5 : ℝ) / A =
        (A / 20 + 11 / 5) / A := by
    field_simp [hA'.ne']
  have hrhs :
      B / (P * O) + M / O = (B + M * P) / (P * O) := by
    field_simp [hP'.ne', hO'.ne']
  rw [hAid, hPid, hOid]
  change 1 / 20 + (11 / 5 : ℝ) / A ≤ B / (P * O) + M / O
  rw [hlhs, hrhs, div_le_div_iff₀ hA' (mul_pos hP' hO')]
  have hcross :
      (B + M * P) * A - (A / 20 + 11 / 5) * (P * O) =
        z * (1672 * z ^ 4 - 5477 * z ^ 3 +
          8558 * z ^ 2 - 6671 * z + 986) / 400 := by
    dsimp [A, P, O, B, M]
    unfold smallPrimeLower smallExpLower
    ring
  rw [← sub_nonneg, hcross]
  exact div_nonneg hnum (by norm_num)

/-- A uniform derivative lower bound for the small-coordinate tangent
comparison throughout all three rounds. -/
lemma tangent_small_coord_prime_lower
    {β₀ β₁ z : ℝ}
    (hβ₀ : β₀ ∈ Set.Icc 0 (2 / 25))
    (hβ₁ : β₁ ∈ Set.Icc 0 (2 / 25))
    (hz : z ∈ Set.Icc 0 (1 / 10)) :
    (1 / 20 : ℝ) ≤ tangentSmallCoordLogPrime β₀ β₁ z := by
  have hd := tangentSmall_domain hβ₁.1 hz
  let p := 1 - tangentBlue β₁ z
  let om := 1 - optimizationM z
  have hp : 0 < p := by exact hd.1
  have hom : 0 < om := by exact hd.2.1
  have hb0 : 0 ≤ tangentBlue β₁ z := by
    unfold tangentBlue
    exact mul_nonneg hz.1 (Real.exp_pos _).le
  have hm0 : 0 ≤ optimizationM z := by
    unfold optimizationM
    exact mul_nonneg hz.1 (Real.exp_pos _).le
  have hp1 : p ≤ 1 := by dsimp [p]; linarith
  have hom1 : om ≤ 1 := by dsimp [om]; linarith
  have hplower := tangent_blue_lower hβ₁ hz
  have hmulower := (tangent_mu_bounds hz).2
  have hpupper : p ≤ smallPUpper z := by
    dsimp [p, smallPUpper]
    linarith
  have homupper : om ≤ smallOmUpper z := by
    dsimp [om, smallOmUpper]
    linarith
  have hP : 0 < smallPUpper z := by
    have hz2 : z ^ 2 ≤ 1 / 100 := by
      nlinarith [mul_nonneg hz.1 (sub_nonneg.mpr hz.2)]
    unfold smallPUpper smallExpLower
    nlinarith
  have hO : 0 < smallOmUpper z := by
    have hz2 : z ^ 2 ≤ 1 / 100 := by
      nlinarith [mul_nonneg hz.1 (sub_nonneg.mpr hz.2)]
    unfold smallOmUpper
    nlinarith
  have hpInv : (smallPUpper z)⁻¹ ≤ p⁻¹ :=
    (inv_le_inv₀ hP hp).mpr hpupper
  have homInv : (smallOmUpper z)⁻¹ ≤ om⁻¹ :=
    (inv_le_inv₀ hO hom).mpr homupper
  have hbp := tangent_blue_prime_lower hβ₁ hz
  have hbp0 : 0 ≤ smallPrimeLower z := by
    unfold smallPrimeLower
    exact mul_nonneg (small_exp_lower_pos hz).le (by
      nlinarith [hz.2])
  have hbpActual0 : 0 ≤ tangentBluePrime β₁ z :=
    hbp0.trans hbp
  have hfirst :
      smallPrimeLower z * (smallPUpper z)⁻¹ *
          (smallOmUpper z)⁻¹ ≤
        tangentBluePrime β₁ z * p⁻¹ * om⁻¹ := by
    calc
      _ ≤ tangentBluePrime β₁ z * (smallPUpper z)⁻¹ *
          (smallOmUpper z)⁻¹ := by
            gcongr
      _ ≤ tangentBluePrime β₁ z * p⁻¹ *
          (smallOmUpper z)⁻¹ := by
            gcongr
      _ ≤ _ := by
            gcongr
  have hmup := (tangent_mu_bounds hz).1
  have hmup0 : 0 ≤ tangentMuPrime z := by
    unfold tangentMuPrime
    exact mul_nonneg (by nlinarith [hz.2]) (Real.exp_pos _).le
  have hsecond :
      (1 - z) ^ 2 * (smallOmUpper z)⁻¹ ≤
        tangentMuPrime z * om⁻¹ := by
    calc
      _ ≤ tangentMuPrime z * (smallOmUpper z)⁻¹ := by
            gcongr
      _ ≤ _ := by
            gcongr
  have hlog : Real.log p ≤ 0 := Real.log_nonpos hp.le hp1
  have hlogterm :
      Real.log p * tangentMuPrime z * om⁻¹ ^ 2 ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg hlog hmup0) (sq_nonneg _)
  have hx :
      tangentXLogPrime β₁ z ≤
        -(smallPrimeLower z /
            (smallPUpper z * smallOmUpper z)) -
          (1 - z) ^ 2 / smallOmUpper z := by
    unfold tangentXLogPrime
    dsimp only
    change
      -tangentBluePrime β₁ z * p⁻¹ * om⁻¹ +
          Real.log p * tangentMuPrime z * om⁻¹ ^ 2 -
          tangentMuPrime z * om⁻¹ ≤ _
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have hPmul : (smallPUpper z * smallOmUpper z)⁻¹ =
        (smallPUpper z)⁻¹ * (smallOmUpper z)⁻¹ := by
      field_simp
    rw [hPmul]
    linarith
  have ha := tangent_alog_prime_lower hβ₀ hz
  have hrat := small_rational_margin hz
  have ha' :
      -(11 / 5 : ℝ) / (1 + (11 / 5) * z) ≤
        (11 / 5) * tangentALogPrime β₀ (tangentSmallT z) := by
    have := mul_le_mul_of_nonneg_left ha (by norm_num : (0 : ℝ) ≤ 11 / 5)
    simpa [tangentSmallT, div_eq_mul_inv] using this
  let r : ℝ := (11 / 5) / (1 + (11 / 5) * z)
  let S : ℝ :=
    smallPrimeLower z / (smallPUpper z * smallOmUpper z) +
      (1 - z) ^ 2 / smallOmUpper z
  have ha'' : -r ≤ (11 / 5) *
      tangentALogPrime β₀ (tangentSmallT z) := by
    simpa [r, neg_div] using ha'
  change (1 / 20 : ℝ) + r ≤ S at hrat
  have hx' : tangentXLogPrime β₁ z ≤ -S := by
    dsimp [S]
    linarith [hx]
  unfold tangentSmallCoordLogPrime
  change (1 / 20 : ℝ) ≤
    (11 / 5) * tangentALogPrime β₀ (tangentSmallT z) -
      tangentXLogPrime β₁ z
  linarith [ha'', hx']

/-- The exponential factor in the tangent blue coordinate is at most `9 / 7`
on the small-book interval. -/
private lemma small_exp_factor_upper {β z : ℝ}
    (hβ : β ∈ Set.Icc 0 (2 / 25))
    (hz : z ∈ Set.Icc 0 (1 / 10)) :
    smallExpFactor β z ≤ 9 / 7 := by
  let C : ℝ :=
    -(1 / 4) + 2 * β * z + 6 / 25 * z ^ 2 -
      (-(1 / 4) * z + β * z ^ 2 + 2 / 25 * z ^ 3)
  have hz2 : z ^ 2 ≤ 1 / 100 := by
    nlinarith [mul_nonneg hz.1 (sub_nonneg.mpr hz.2)]
  have hz3 : z ^ 3 ≤ 1 / 1000 := by
    nlinarith [mul_nonneg (sq_nonneg z) (sub_nonneg.mpr hz.2)]
  have hβz : β * z ≤ (2 / 25 : ℝ) * (1 / 10) :=
    mul_le_mul hβ.2 hz.2 hz.1 (by norm_num)
  have hC0 : C ≤ 0 := by
    dsimp [C]
    nlinarith [mul_nonneg hβ.1 (sq_nonneg z),
      mul_nonneg (sq_nonneg z) hz.1]
  have hClo : -(1 / 4 : ℝ) ≤ C := by
    have hcoef : 0 ≤ 6 / 25 - β := by
      linarith [hβ.2]
    have hmain :
        0 ≤ 2 * β * z + (6 / 25 - β) * z ^ 2 := by
      exact add_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) hβ.1) hz.1)
        (mul_nonneg hcoef (sq_nonneg z))
    have htail : 0 ≤ (1 / 4 : ℝ) * z - 2 / 25 * z ^ 3 := by
      have hfactor : 0 ≤ (1 / 4 : ℝ) - 2 / 25 * z ^ 2 := by
        nlinarith [hz2]
      have hid :
          (1 / 4 : ℝ) * z - 2 / 25 * z ^ 3 =
            z * (1 / 4 - 2 / 25 * z ^ 2) := by ring
      rw [hid]
      exact mul_nonneg hz.1 hfactor
    dsimp [C]
    linarith
  have he1 := (exp_neg_bounds hz).2
  have hcorr : -(1 / 4 : ℝ) ≤ tangentCorrectionSlope β z := by
    have hmul : C ≤ C * Real.exp (-z) := by
      simpa only [mul_one] using mul_le_mul_of_nonpos_left he1 hC0
    change -(1 / 4 : ℝ) ≤ C * Real.exp (-z)
    exact hClo.trans hmul
  have hlog : 0 ≤ Real.log (1 + z) :=
    Real.log_nonneg (by linarith [hz.1])
  have hexponent :
      -Real.log (1 + z) - tangentCorrectionSlope β z ≤ 1 / 4 := by
    linarith
  have hlog97 := KernelBounds.log_lower_of_one_le
    (x := (9 / 7 : ℝ)) (by norm_num)
  have hquarter : (1 / 4 : ℝ) ≤ Real.log (9 / 7) := by
    norm_num at hlog97 ⊢
    linarith
  calc
    smallExpFactor β z ≤ Real.exp (1 / 4) := by
      unfold smallExpFactor
      exact Real.exp_le_exp.mpr hexponent
    _ ≤ Real.exp (Real.log (9 / 7)) :=
      Real.exp_le_exp.mpr hquarter
    _ = 9 / 7 := Real.exp_log (by norm_num)

private lemma correction_slope_deriv_lower {β z : ℝ}
    (hβ : β ∈ Set.Icc 0 (2 / 25))
    (hz : z ∈ Set.Icc 0 (1 / 10)) :
    z ≤ tangentCorrectionSlopeDeriv β z := by
  let D : ℝ :=
    (2 * β + 12 / 25 * z -
        (-(1 / 4) + 2 * β * z + 6 / 25 * z ^ 2)) -
      (-(1 / 4) + 2 * β * z + 6 / 25 * z ^ 2 -
        (-(1 / 4) * z + β * z ^ 2 + 2 / 25 * z ^ 3))
  have hDid :
      D = 1 / 2 + 2 * β - 4 * β * z + β * z ^ 2 +
        23 / 100 * z - 12 / 25 * z ^ 2 + 2 / 25 * z ^ 3 := by
    dsimp [D]
    ring
  have hz2 : z ^ 2 ≤ 1 / 100 := by
    nlinarith [mul_nonneg hz.1 (sub_nonneg.mpr hz.2)]
  have hβz : β * z ≤ (2 / 25 : ℝ) * (1 / 10) :=
    mul_le_mul hβ.2 hz.2 hz.1 (by norm_num)
  have hD : (2 / 5 : ℝ) ≤ D := by
    have hbase :
        (2 / 5 : ℝ) ≤ 1 / 2 - 4 * β * z - 12 / 25 * z ^ 2 := by
      nlinarith
    have hrest :
        0 ≤ 2 * β + β * z ^ 2 +
          23 / 100 * z + 2 / 25 * z ^ 3 := by
      exact add_nonneg
        (add_nonneg
          (add_nonneg (mul_nonneg (by norm_num) hβ.1)
            (mul_nonneg hβ.1 (sq_nonneg z)))
          (mul_nonneg (by norm_num) hz.1))
        (mul_nonneg (by norm_num)
          (mul_nonneg (sq_nonneg z) hz.1))
    rw [hDid]
    linarith
  have he := (exp_neg_bounds hz).1
  have hz1 : 0 ≤ 1 - z := by linarith [hz.2]
  have hmul :
      (2 / 5 : ℝ) * (1 - z) ≤ D * Real.exp (-z) :=
    mul_le_mul hD he hz1 (le_trans (by norm_num) hD)
  have hzbound : z ≤ (2 / 5 : ℝ) * (1 - z) := by
    nlinarith [hz.2]
  change z ≤ D * Real.exp (-z)
  exact hzbound.trans hmul

private lemma tangent_blue_prime_upper {β z : ℝ}
    (hβ : β ∈ Set.Icc 0 (2 / 25))
    (hz : z ∈ Set.Icc 0 (1 / 50)) :
    tangentBluePrime β z ≤ (9 / 7) * (1 - z) := by
  have hz' : z ∈ Set.Icc (0 : ℝ) (1 / 10) := by
    constructor
    · exact hz.1
    · nlinarith [hz.2]
  have he := small_exp_factor_upper hβ hz'
  have hd := correction_slope_deriv_lower hβ hz'
  have hzplus : 0 < 1 + z := by linarith [hz.1]
  have hinv : 1 - z ≤ (1 + z)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hzplus]
    nlinarith [sq_nonneg z]
  let F : ℝ :=
    1 - z * ((1 + z)⁻¹ + tangentCorrectionSlopeDeriv β z)
  have hF : F ≤ 1 - z := by
    dsimp [F]
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add hinv hd) hz.1]
  have hF0 : 0 ≤ F := by
    have hd' := correction_slope_deriv_upper hβ hz'
    have hinv' : (1 + z)⁻¹ ≤ 1 :=
      (inv_le_one₀ hzplus).mpr (by linarith [hz.1])
    dsimp [F]
    nlinarith [mul_le_mul_of_nonneg_left
      (add_le_add hinv' hd') hz.1, hz.2]
  have hz1 : 0 ≤ 1 - z := by linarith [hz.2]
  change smallExpFactor β z * F ≤ (9 / 7) * (1 - z)
  exact mul_le_mul he hF hF0 (by norm_num)

private lemma tangent_xlog_prime_small_lower {β z : ℝ}
    (hβ : β ∈ Set.Icc 0 (2 / 25))
    (hz : z ∈ Set.Icc 0 (1 / 50)) :
    -(9 / 7) / (1 - (9 / 7) * z) - 1 - 3 / 98 ≤
      tangentXLogPrime β z := by
  have hz' : z ∈ Set.Icc (0 : ℝ) (1 / 10) := by
    constructor
    · exact hz.1
    · nlinarith [hz.2]
  have hd := tangentSmall_domain hβ.1 hz'
  let p := 1 - tangentBlue β z
  let om := 1 - optimizationM z
  let pL : ℝ := 1 - (9 / 7) * z
  have hp : 0 < p := hd.1
  have hom : 0 < om := hd.2.1
  have he := small_exp_factor_upper hβ hz'
  have hblue : tangentBlue β z ≤ (9 / 7) * z := by
    unfold tangentBlue
    simpa [smallExpFactor, mul_comm] using
      mul_le_mul_of_nonneg_left he hz.1
  have hpL : 0 < pL := by
    dsimp [pL]
    nlinarith [hz.2]
  have hpLower : pL ≤ p := by
    dsimp [pL, p]
    linarith
  have hpInv : p⁻¹ ≤ pL⁻¹ :=
    (inv_le_inv₀ hp hpL).mpr hpLower
  have heNeg := (exp_neg_bounds hz').1
  have homLower : 1 - z ≤ om := by
    dsimp [om]
    unfold optimizationM
    nlinarith [mul_le_mul_of_nonneg_left
      (exp_neg_bounds hz').2 hz.1]
  have hOneSub : 0 < 1 - z := by linarith [hz.2]
  have homInv : om⁻¹ ≤ (1 - z)⁻¹ :=
    (inv_le_inv₀ hom hOneSub).mpr homLower
  have hbp := tangent_blue_prime_upper hβ hz
  have hbp0 : 0 ≤ tangentBluePrime β z := by
    have hlower := tangent_blue_prime_lower hβ hz'
    have hlower0 : 0 ≤ smallPrimeLower z := by
      unfold smallPrimeLower
      exact mul_nonneg (small_exp_lower_pos hz').le (by
        nlinarith [hz.2])
    exact hlower0.trans hlower
  have hfirst :
      tangentBluePrime β z * p⁻¹ * om⁻¹ ≤
        (9 / 7) * pL⁻¹ := by
    calc
      _ ≤ ((9 / 7) * (1 - z)) * pL⁻¹ * (1 - z)⁻¹ := by
        gcongr
      _ = (9 / 7) * pL⁻¹ := by
        field_simp [hOneSub.ne']
  have hmup0 : 0 ≤ tangentMuPrime z := by
    unfold tangentMuPrime
    exact mul_nonneg (by linarith [hz.2]) (Real.exp_pos _).le
  have hmupOm : tangentMuPrime z * om⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hom]
    dsimp [om]
    unfold tangentMuPrime optimizationM
    have he1 := (exp_neg_bounds hz').2
    nlinarith [mul_le_mul_of_nonneg_left he1 (by
      linarith [hz.2] : 0 ≤ 1 - z)]
  have hp1 : p ≤ 1 := by
    dsimp [p]
    unfold tangentBlue
    exact sub_le_self _ (mul_nonneg hz.1 (Real.exp_pos _).le)
  have hlogUpper : Real.log p ≤ 0 := Real.log_nonpos hp.le hp1
  have hpRat : (341 / 350 : ℝ) ≤ p := by
    dsimp [pL] at hpLower
    nlinarith [hz.2]
  have hq : (0 : ℝ) < 341 / 350 := by norm_num
  have hpInvRat : p⁻¹ ≤ (341 / 350 : ℝ)⁻¹ :=
    (inv_le_inv₀ hp hq).mpr hpRat
  have hlogRaw := KernelBounds.log_lower_of_le_one hp hp1
  have hlogLower : -(3 / 100 : ℝ) ≤ Real.log p := by
    norm_num at hpInvRat
    nlinarith
  have homRat : (49 / 50 : ℝ) ≤ om := by
    dsimp [om]
    unfold optimizationM
    have he1 := (exp_neg_bounds hz').2
    nlinarith [mul_le_mul_of_nonneg_left he1 hz.1, hz.2]
  have hqom : (0 : ℝ) < 49 / 50 := by norm_num
  have homInvRat : om⁻¹ ≤ (50 / 49 : ℝ) := by
    have := (inv_le_inv₀ hom hqom).mpr homRat
    norm_num at this ⊢
    exact this
  have hcoeff :
      tangentMuPrime z * om⁻¹ ^ 2 ≤ 50 / 49 := by
    have hrewrite :
        tangentMuPrime z * om⁻¹ ^ 2 =
          (tangentMuPrime z * om⁻¹) * om⁻¹ := by ring
    rw [hrewrite]
    calc
      (tangentMuPrime z * om⁻¹) * om⁻¹ ≤ 1 * om⁻¹ :=
        mul_le_mul_of_nonneg_right hmupOm (inv_nonneg.mpr hom.le)
      _ ≤ 1 * (50 / 49) :=
        mul_le_mul_of_nonneg_left homInvRat (by norm_num)
      _ = 50 / 49 := one_mul _
  have hcoeff0 : 0 ≤ tangentMuPrime z * om⁻¹ ^ 2 := by
    exact mul_nonneg hmup0 (sq_nonneg _)
  have hlogterm :
      -(3 / 98 : ℝ) ≤
        Real.log p * tangentMuPrime z * om⁻¹ ^ 2 := by
    calc
      -(3 / 98 : ℝ) =
          (-(3 / 100 : ℝ)) * (50 / 49) := by norm_num
      _ ≤ Real.log p * (50 / 49) :=
        mul_le_mul_of_nonneg_right hlogLower (by norm_num)
      _ ≤ Real.log p * (tangentMuPrime z * om⁻¹ ^ 2) :=
        mul_le_mul_of_nonpos_left hcoeff hlogUpper
      _ = Real.log p * tangentMuPrime z * om⁻¹ ^ 2 := by ring
  unfold tangentXLogPrime
  dsimp only
  change _ ≤
    -tangentBluePrime β z * p⁻¹ * om⁻¹ +
      Real.log p * tangentMuPrime z * om⁻¹ ^ 2 -
      tangentMuPrime z * om⁻¹
  rw [div_eq_mul_inv]
  linarith

private lemma small_y_log_lower {β z : ℝ}
    (hβ : β ∈ Set.Icc 0 (2 / 25))
    (hz : z ∈ Set.Icc 0 (1 / 50)) :
    (265 / 256 : ℝ) - (22 / 5) * z ≤
      tangentSmallYLogOverZ β z := by
  let t := tangentSmallT z
  have ht : t ∈ Set.Icc (0 : ℝ) (1 / 10) := by
    dsimp [t, tangentSmallT]
    constructor
    · nlinarith [hz.1]
    · nlinarith [hz.2]
  have hlogConst := KernelBounds.log_lower_of_one_le
    (x := (11 / 5 : ℝ)) (by norm_num)
  have hlogConst' : (201 / 256 : ℝ) ≤ Real.log (11 / 5) := by
    norm_num at hlogConst ⊢
    linarith
  have hlogT := Real.log_le_sub_one_of_pos
    (by linarith [ht.1] : 0 < 1 + t)
  have hcorr := correction_slope_upper hβ ht
  unfold tangentSmallYLogOverZ
  change _ ≤ Real.log (11 / 5) - Real.log (1 + t) -
    tangentCorrectionSlope β t
  dsimp [t, tangentSmallT] at hlogT hcorr ⊢
  norm_num at hlogT ⊢
  linarith

private lemma small_y_log_prime_lower {β z : ℝ}
    (hβ : β ∈ Set.Icc 0 (2 / 25))
    (hz : z ∈ Set.Icc 0 (1 / 50)) :
    -(77 / 20 : ℝ) ≤ tangentSmallYLogOverZPrime β z := by
  let t := tangentSmallT z
  have ht : t ∈ Set.Icc (0 : ℝ) (1 / 10) := by
    dsimp [t, tangentSmallT]
    constructor
    · nlinarith [hz.1]
    · nlinarith [hz.2]
  have htplus : 0 < 1 + t := by linarith [ht.1]
  have hinv : (1 + t)⁻¹ ≤ 1 :=
    (inv_le_one₀ htplus).mpr (by linarith [ht.1])
  have hd := correction_slope_deriv_upper hβ ht
  unfold tangentSmallYLogOverZPrime
  change _ ≤ -(11 / 5) *
    ((1 + t)⁻¹ + tangentCorrectionSlopeDeriv β t)
  nlinarith

private lemma small_book_rational_margin {z : ℝ}
    (hz : z ∈ Set.Icc 0 (1 / 50)) :
    (1 / 1000 : ℝ) ≤
      2 * z / (z + 2) + 3 / 4 +
        (-(9 / 7) / (1 - (9 / 7) * z) - 1 - 3 / 98 +
          265 / 256 - 41 / 4 * z) / 2 := by
  have hp : 0 < 1 - (9 / 7 : ℝ) * z := by
    nlinarith [hz.2]
  have hzplus : 0 < z + 2 := by linarith [hz.1]
  have hnum :
      0 ≤ 4759846 - 221131879 * z + 99140099 * z ^ 2 +
        144648000 * z ^ 3 := by
    nlinarith [hz.2, sq_nonneg z,
      mul_nonneg (sq_nonneg z) hz.1]
  have hden : 0 < 7 - 9 * z := by nlinarith [hz.2]
  have hden' : 0 < 7 - z * 9 := by nlinarith [hz.2]
  have hfrac :
      -(9 / 7 : ℝ) / (1 - (9 / 7) * z) =
        -9 / (7 - 9 * z) := by
    field_simp [hp.ne', hden.ne']
  have hid :
      2 * z / (z + 2) + 3 / 4 +
            (-(9 / 7) / (1 - (9 / 7) * z) - 1 - 3 / 98 +
              265 / 256 - 41 / 4 * z) / 2 -
          1 / 1000 =
        (4759846 - 221131879 * z + 99140099 * z ^ 2 +
            144648000 * z ^ 3) /
          (3136000 * (z + 2) * (7 - 9 * z)) := by
    rw [hfrac]
    field_simp [hden.ne', hden'.ne', hzplus.ne']
    ring
  rw [← sub_nonneg, hid]
  exact div_nonneg hnum
    (mul_nonneg (mul_nonneg (by norm_num) hzplus.le) hden.le)

/-- A uniform derivative lower bound for the small-book comparison throughout
all three tangent rounds. -/
lemma tangent_small_book_prime_lower
    {β₀ β₁ z : ℝ}
    (hβ₀ : β₀ ∈ Set.Icc 0 (2 / 25))
    (hβ₁ : β₁ ∈ Set.Icc 0 (2 / 25))
    (hz : z ∈ Set.Icc 0 (1 / 50)) :
    (1 / 1000 : ℝ) ≤ tangentSmallBookMarginPrime β₀ β₁ z := by
  have hz' : z ∈ Set.Icc (0 : ℝ) (1 / 10) := by
    constructor
    · exact hz.1
    · nlinarith [hz.2]
  have hcorr : -(1 / 4 : ℝ) ≤ tangentCorrectionSlope β₁ z := by
    -- Reuse the lower-bound argument embedded in the factor estimate.
    let C : ℝ :=
      -(1 / 4) + 2 * β₁ * z + 6 / 25 * z ^ 2 -
        (-(1 / 4) * z + β₁ * z ^ 2 + 2 / 25 * z ^ 3)
    have hC0 : C ≤ 0 := by
      dsimp [C]
      have hz2 : z ^ 2 ≤ 1 / 100 := by
        nlinarith [mul_nonneg hz'.1 (sub_nonneg.mpr hz'.2)]
      have hz3 : z ^ 3 ≤ 1 / 1000 := by
        nlinarith [mul_nonneg (sq_nonneg z) (sub_nonneg.mpr hz'.2)]
      have hβz : β₁ * z ≤ (2 / 25 : ℝ) * (1 / 10) :=
        mul_le_mul hβ₁.2 hz'.2 hz'.1 (by norm_num)
      nlinarith [mul_nonneg hβ₁.1 (sq_nonneg z),
        mul_nonneg (sq_nonneg z) hz'.1]
    have hClo : -(1 / 4 : ℝ) ≤ C := by
      have hcoef : 0 ≤ 6 / 25 - β₁ := by linarith [hβ₁.2]
      have hmain :
          0 ≤ 2 * β₁ * z + (6 / 25 - β₁) * z ^ 2 := by
        exact add_nonneg
          (mul_nonneg (mul_nonneg (by norm_num) hβ₁.1) hz.1)
          (mul_nonneg hcoef (sq_nonneg z))
      have htail : 0 ≤ (1 / 4 : ℝ) * z - 2 / 25 * z ^ 3 := by
        have hz2 : z ^ 2 ≤ 1 / 100 := by
          nlinarith [mul_nonneg hz.1 (sub_nonneg.mpr hz'.2)]
        have hfactor : 0 ≤ (1 / 4 : ℝ) - 2 / 25 * z ^ 2 := by
          nlinarith
        have hid :
            (1 / 4 : ℝ) * z - 2 / 25 * z ^ 3 =
              z * (1 / 4 - 2 / 25 * z ^ 2) := by ring
        rw [hid]
        exact mul_nonneg hz.1 hfactor
      dsimp [C]
      linarith
    have he1 := (exp_neg_bounds hz').2
    have hmul : C ≤ C * Real.exp (-z) := by
      simpa only [mul_one] using mul_le_mul_of_nonpos_left he1 hC0
    change -(1 / 4 : ℝ) ≤ C * Real.exp (-z)
    exact hClo.trans hmul
  have hlog := Real.le_log_one_add_of_nonneg hz.1
  have hx := tangent_xlog_prime_small_lower hβ₁ hz
  have hy := small_y_log_lower hβ₀ hz
  have hyp := small_y_log_prime_lower hβ₀ hz
  have hzHyp :
      -(77 / 20 : ℝ) * z ≤
        z * tangentSmallYLogOverZPrime β₀ z :=
    by
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hyp hz.1
  have hrat := small_book_rational_margin hz
  unfold tangentSmallBookMarginPrime
  linarith

private def smallBookExpUpper (z : ℝ) : ℝ :=
  9 / 7 - 7 / 4 * z

private lemma small_book_exp_factor_upper {β z : ℝ}
    (hβ : β ∈ Set.Icc (3 / 100) (2 / 25))
    (hz : z ∈ Set.Icc 0 (1 / 10)) :
    smallExpFactor β z ≤ smallBookExpUpper z := by
  let C : ℝ :=
    -(1 / 4) + 2 * β * z + 6 / 25 * z ^ 2 -
      (-(1 / 4) * z + β * z ^ 2 + 2 / 25 * z ^ 3)
  let L : ℝ :=
    -(1 / 4) + 1 / 4 * z + 6 / 25 * z ^ 2 -
      2 / 25 * z ^ 3 + 3 / 100 * z * (2 - z)
  have hL0 : L ≤ 0 := by
    have hz2 : z ^ 2 ≤ 1 / 100 := by
      nlinarith [mul_nonneg hz.1 (sub_nonneg.mpr hz.2)]
    have hz3 : z ^ 3 ≤ 1 / 1000 := by
      nlinarith [mul_nonneg (sq_nonneg z) hz.1, hz.2]
    dsimp [L]
    nlinarith [hz.1, hz2, hz3]
  have hLC : L ≤ C := by
    have hβ : 0 ≤ β - 3 / 100 := sub_nonneg.mpr hβ.1
    have hzTwo : 0 ≤ 2 - z := by linarith [hz.2]
    have hprod : 0 ≤ (β - 3 / 100) * z * (2 - z) :=
      mul_nonneg (mul_nonneg hβ hz.1) hzTwo
    dsimp [L, C]
    nlinarith
  have hzplus : 0 < 1 + z := by linarith [hz.1]
  have hez : 1 + z ≤ Real.exp z := by
    linarith [Real.add_one_le_exp z]
  have heUpper : Real.exp (-z) ≤ (1 + z)⁻¹ := by
    rw [Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos z) hzplus).mpr hez
  have hcorrLower :
      L / (1 + z) ≤ tangentCorrectionSlope β z := by
    calc
      L / (1 + z) = L * (1 + z)⁻¹ := div_eq_mul_inv _ _
      _ ≤ L * Real.exp (-z) :=
        mul_le_mul_of_nonpos_left heUpper hL0
      _ ≤ C * Real.exp (-z) :=
        mul_le_mul_of_nonneg_right hLC (Real.exp_pos _).le
      _ = tangentCorrectionSlope β z := by
        unfold tangentCorrectionSlope
        dsimp [C]
  have hlogLower :
      2 * z / (z + 2) ≤ Real.log (1 + z) := by
    simpa [add_comm] using Real.le_log_one_add_of_nonneg hz.1
  let U : ℝ := -2 * z / (z + 2) - L / (1 + z)
  have hexponent :
      -Real.log (1 + z) - tangentCorrectionSlope β z ≤ U := by
    calc
      -Real.log (1 + z) - tangentCorrectionSlope β z ≤
          -(2 * z / (z + 2)) - tangentCorrectionSlope β z :=
        sub_le_sub_right (neg_le_neg hlogLower) _
      _ ≤ -(2 * z / (z + 2)) - L / (1 + z) :=
        sub_le_sub_left hcorrLower _
      _ = U := by
        dsimp [U]
        ring
  let R : ℝ := smallBookExpUpper z
  have hRone : 1 ≤ R := by
    dsimp [R, smallBookExpUpper]
    nlinarith [hz.2]
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hRone
  have hRplus : 0 < R + 1 := by positivity
  have hlogR :
      2 * (R - 1) / (R + 1) ≤ Real.log R := by
    have h := Real.le_log_one_add_of_nonneg
      (x := R - 1) (sub_nonneg.mpr hRone)
    convert h using 1 <;> ring_nf
  have hzplusTwo : 0 < z + 2 := by linarith [hz.1]
  have hden : 0 < 64 - 49 * z := by nlinarith [hz.2]
  have hpoly :
      0 ≤ 392 * z ^ 4 - 757 * z ^ 3 - 22857 * z ^ 2 -
        21941 * z + 2818 := by
    have hz2 : z ^ 2 ≤ 1 / 100 := by
      nlinarith [mul_nonneg hz.1 (sub_nonneg.mpr hz.2)]
    have hz3 : z ^ 3 ≤ 1 / 1000 := by
      nlinarith [mul_nonneg (sq_nonneg z) hz.1, hz.2]
    have hz4 : z ^ 4 ≤ 1 / 10000 := by
      nlinarith [sq_nonneg (z ^ 2), hz2]
    nlinarith [hz.2, hz2, hz3, hz4]
  have hrat : U ≤ 2 * (R - 1) / (R + 1) := by
    have hOne : 1 + z ≠ 0 := hzplus.ne'
    have hOne' : z + 1 ≠ 0 := by linarith [hzplus]
    have hprod :
        0 < 100 * (z + 1) * (z + 2) * (64 - 49 * z) := by
      exact mul_pos
        (mul_pos (mul_pos (by norm_num) (by linarith [hzplus]))
          hzplusTwo) hden
    have hRrat :
        2 * (R - 1) / (R + 1) =
          2 * (8 - 49 * z) / (64 - 49 * z) := by
      apply (div_eq_div_iff hRplus.ne' hden.ne').2
      dsimp [R, smallBookExpUpper]
      ring
    have hid :
        2 * (8 - 49 * z) / (64 - 49 * z) - U =
          z * (392 * z ^ 4 - 757 * z ^ 3 - 22857 * z ^ 2 -
              21941 * z + 2818) /
            (100 * (z + 1) * (z + 2) * (64 - 49 * z)) := by
      dsimp [U, L]
      field_simp [hOne, hOne', hzplusTwo.ne', hden.ne']
      ring
    rw [hRrat, ← sub_nonneg, hid]
    exact div_nonneg (mul_nonneg hz.1 hpoly) hprod.le
  calc
    smallExpFactor β z ≤ Real.exp U := by
      unfold smallExpFactor
      exact Real.exp_le_exp.mpr hexponent
    _ ≤ Real.exp (Real.log R) :=
      Real.exp_le_exp.mpr (hrat.trans hlogR)
    _ = R := Real.exp_log hRpos
    _ = smallBookExpUpper z := rfl

private def smallBookP (z : ℝ) : ℝ :=
  1 - z * smallBookExpUpper z

private def smallBookO (z : ℝ) : ℝ :=
  (1 + z)⁻¹

private def smallBookRamseyLower (z : ℝ) : ℝ :=
  (-(1 / 4) * z + 3 / 100 * z ^ 2 + 2 / 25 * z ^ 3) /
    (1 + z)

private def smallBookExpLower (t : ℝ) : ℝ :=
  1 - t + t ^ 2 / 2 - t ^ 3 / 6 - 5 / 96 * t ^ 4

private def smallBookLogUpper (t : ℝ) : ℝ :=
  t - t ^ 2 / 2 + t ^ 3 / 3 + t ^ 4 / (1 - t)

private def smallBookCorrectionUpper (t : ℝ) : ℝ :=
  -(1 / 4) + 41 / 100 * t + 4 / 25 * t ^ 2 -
    2 / 25 * t ^ 3

private def smallBookYLower (z : ℝ) : ℝ :=
  let t := 11 / 5 * z
  63 / 80 - smallBookLogUpper t -
    smallBookCorrectionUpper t * smallBookExpLower t

private def smallBookXLower (z : ℝ) : ℝ :=
  (smallBookP z - (smallBookP z)⁻¹) / 2 * (smallBookO z)⁻¹ +
    (smallBookO z - (smallBookO z)⁻¹) / 2

private def smallBookValueLower (z : ℝ) : ℝ :=
  (1 + z) * (2 * z / (z + 2)) +
    smallBookRamseyLower z +
    (smallBookXLower z - z ^ 2 + z * smallBookYLower z) / 2

private lemma log_eleven_fifths_lower :
    (63 / 80 : ℝ) ≤ Real.log (11 / 5) := by
  have h := Real.sum_range_le_log_div
    (x := (3 / 8 : ℝ)) (by norm_num) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h
  linarith

private lemma exp_neg_lower_small {t : ℝ}
    (ht : t ∈ Set.Icc 0 (11 / 50)) :
    smallBookExpLower t ≤ Real.exp (-t) := by
  have habs : |-t| ≤ 1 := by
    rw [abs_neg, abs_of_nonneg ht.1]
    linarith [ht.2]
  have h := Real.exp_bound (x := -t) (n := 4) habs (by norm_num)
  have hlow := (abs_le.mp h).1
  norm_num [Finset.sum_range_succ, Nat.factorial,
    abs_neg, abs_of_nonneg ht.1, smallBookExpLower] at hlow ⊢
  linarith

private lemma log_one_add_upper_small {t : ℝ}
    (ht : t ∈ Set.Icc 0 (11 / 50)) :
    Real.log (1 + t) ≤ smallBookLogUpper t := by
  have habs : |-t| < 1 := by
    rw [abs_neg, abs_of_nonneg ht.1]
    linarith [ht.2]
  have h := Real.abs_log_sub_add_sum_range_le
    (x := -t) habs 3
  have hu := (abs_le.mp h).2
  norm_num [Finset.sum_range_succ, abs_neg,
    abs_of_nonneg ht.1, smallBookLogUpper] at hu ⊢
  linarith

private lemma small_book_y_lower {β z : ℝ}
    (hβ : β ∈ Set.Icc 0 (2 / 25))
    (hz : z ∈ Set.Icc 0 (1 / 10)) :
    smallBookYLower z ≤ tangentSmallYLogOverZ β z := by
  let t : ℝ := 11 / 5 * z
  have ht : t ∈ Set.Icc (0 : ℝ) (11 / 50) := by
    dsimp [t]
    constructor <;> nlinarith [hz.1, hz.2]
  let C : ℝ :=
    -(1 / 4) + 2 * β * t + 6 / 25 * t ^ 2 -
      (-(1 / 4) * t + β * t ^ 2 + 2 / 25 * t ^ 3)
  let U : ℝ := smallBookCorrectionUpper t
  have hCU : C ≤ U := by
    have hcoef : 0 ≤ 2 / 25 - β := sub_nonneg.mpr hβ.2
    have htTwo : 0 ≤ 2 - t := by linarith [ht.2]
    have hprod : 0 ≤ (2 / 25 - β) * t * (2 - t) :=
      mul_nonneg (mul_nonneg hcoef ht.1) htTwo
    dsimp [C, U, smallBookCorrectionUpper]
    nlinarith
  have hU0 : U ≤ 0 := by
    have ht2 : t ^ 2 ≤ (11 / 50 : ℝ) ^ 2 := by
      nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]
    have ht3 : t ^ 3 ≤ (11 / 50 : ℝ) ^ 3 := by
      nlinarith [mul_nonneg (sq_nonneg t) ht.1, ht.2, ht2]
    dsimp [U, smallBookCorrectionUpper]
    nlinarith [ht.2, ht2, ht3]
  have heLower := exp_neg_lower_small ht
  have hcorr :
      tangentCorrectionSlope β t ≤
        smallBookCorrectionUpper t * smallBookExpLower t := by
    calc
      tangentCorrectionSlope β t = C * Real.exp (-t) := by
        unfold tangentCorrectionSlope
        dsimp [C]
      _ ≤ U * Real.exp (-t) :=
        mul_le_mul_of_nonneg_right hCU (Real.exp_pos _).le
      _ ≤ U * smallBookExpLower t :=
        mul_le_mul_of_nonpos_left heLower hU0
      _ = smallBookCorrectionUpper t * smallBookExpLower t := rfl
  have hlogUpper := log_one_add_upper_small ht
  unfold tangentSmallYLogOverZ
  change smallBookYLower z ≤
    Real.log (11 / 5) - Real.log (1 + t) -
      tangentCorrectionSlope β t
  dsimp [smallBookYLower, t]
  linarith [log_eleven_fifths_lower]

private lemma small_book_ramsey_lower {β z : ℝ}
    (hβ : β ∈ Set.Icc (3 / 100) (2 / 25))
    (hz : z ∈ Set.Icc 0 (1 / 10)) :
    smallBookRamseyLower z ≤ ramseyCorrection β z := by
  let P : ℝ := -(1 / 4) * z + β * z ^ 2 + 2 / 25 * z ^ 3
  let L : ℝ := -(1 / 4) * z + 3 / 100 * z ^ 2 + 2 / 25 * z ^ 3
  have hL0 : L ≤ 0 := by
    have hz2 : z ^ 2 ≤ 1 / 100 := by
      nlinarith [mul_nonneg hz.1 (sub_nonneg.mpr hz.2)]
    have hz3 : z ^ 3 ≤ 1 / 1000 := by
      nlinarith [mul_nonneg (sq_nonneg z) hz.1, hz.2]
    dsimp [L]
    nlinarith [hz.1, hz2, hz3]
  have hLP : L ≤ P := by
    have hcoef : 0 ≤ β - 3 / 100 := sub_nonneg.mpr hβ.1
    have hprod : 0 ≤ (β - 3 / 100) * z ^ 2 :=
      mul_nonneg hcoef (sq_nonneg z)
    dsimp [L, P]
    nlinarith
  have hzplus : 0 < 1 + z := by linarith [hz.1]
  have hez : 1 + z ≤ Real.exp z := by
    linarith [Real.add_one_le_exp z]
  have heUpper : Real.exp (-z) ≤ (1 + z)⁻¹ := by
    rw [Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos z) hzplus).mpr hez
  calc
    smallBookRamseyLower z = L * (1 + z)⁻¹ := by
      dsimp [smallBookRamseyLower, L]
      rw [div_eq_mul_inv]
    _ ≤ L * Real.exp (-z) :=
      mul_le_mul_of_nonpos_left heUpper hL0
    _ ≤ P * Real.exp (-z) :=
      mul_le_mul_of_nonneg_right hLP (Real.exp_pos _).le
    _ = ramseyCorrection β z := by
      unfold ramseyCorrection
      dsimp [P]

private lemma small_book_x_lower {β z : ℝ}
    (hβ : β ∈ Set.Icc (3 / 100) (2 / 25))
    (hz : z ∈ Set.Icc 0 (1 / 10)) :
    smallBookXLower z ≤ tangentXLog β z := by
  have hd := tangentSmall_domain
    (le_trans (by norm_num : (0 : ℝ) ≤ 3 / 100) hβ.1) hz
  let p : ℝ := 1 - tangentBlue β z
  let om : ℝ := 1 - optimizationM z
  let P : ℝ := smallBookP z
  let O : ℝ := smallBookO z
  have hp : 0 < p := hd.1
  have hom : 0 < om := hd.2.1
  have hb0 : 0 ≤ tangentBlue β z := by
    unfold tangentBlue
    exact mul_nonneg hz.1 (Real.exp_pos _).le
  have hm0 : 0 ≤ optimizationM z := by
    unfold optimizationM
    exact mul_nonneg hz.1 (Real.exp_pos _).le
  have hp1 : p ≤ 1 := by dsimp [p]; linarith
  have hom1 : om ≤ 1 := by dsimp [om]; linarith
  have hfactor := small_book_exp_factor_upper hβ hz
  have hblue :
      tangentBlue β z ≤ z * smallBookExpUpper z := by
    change z * smallExpFactor β z ≤ z * smallBookExpUpper z
    exact mul_le_mul_of_nonneg_left hfactor hz.1
  have hPp : P ≤ p := by
    dsimp [P, p, smallBookP]
    linarith
  have hP : 0 < P := by
    dsimp [P, smallBookP, smallBookExpUpper]
    have hz2 : z ^ 2 ≤ 1 / 100 := by
      nlinarith [mul_nonneg hz.1 (sub_nonneg.mpr hz.2)]
    nlinarith [hz.2, hz2]
  have hzplus : 0 < 1 + z := by linarith [hz.1]
  have hez : 1 + z ≤ Real.exp z := by
    linarith [Real.add_one_le_exp z]
  have heUpper : Real.exp (-z) ≤ (1 + z)⁻¹ := by
    rw [Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos z) hzplus).mpr hez
  have hmUpper :
      optimizationM z ≤ z * (1 + z)⁻¹ := by
    unfold optimizationM
    exact mul_le_mul_of_nonneg_left heUpper hz.1
  have hOom : O ≤ om := by
    dsimp [O, om, smallBookO]
    have hid : 1 - z * (1 + z)⁻¹ = (1 + z)⁻¹ := by
      field_simp [hzplus.ne']
      ring
    linarith
  have hO : 0 < O := by
    dsimp [O, smallBookO]
    positivity
  have hpInv : p⁻¹ ≤ P⁻¹ :=
    (inv_le_inv₀ hp hP).mpr hPp
  have homInv : om⁻¹ ≤ O⁻¹ :=
    (inv_le_inv₀ hom hO).mpr hOom
  have hLP :
      (P - P⁻¹) / 2 ≤ (p - p⁻¹) / 2 := by
    linarith
  have hLO :
      (O - O⁻¹) / 2 ≤ (om - om⁻¹) / 2 := by
    linarith
  have hLP0 : (P - P⁻¹) / 2 ≤ 0 := by
    have hP1 : P ≤ 1 := by
      dsimp [P, smallBookP]
      have hExp0 : 0 ≤ smallBookExpUpper z := by
        dsimp [smallBookExpUpper]
        nlinarith [hz.2]
      nlinarith [mul_nonneg hz.1 hExp0]
    have hOneInv : 1 ≤ P⁻¹ := by
      exact (one_le_inv₀ hP).mpr hP1
    linarith
  have hlogP := KernelBounds.log_lower_of_le_one hp hp1
  have hlogO := KernelBounds.log_lower_of_le_one hom hom1
  have hfirst :
      (P - P⁻¹) / 2 * O⁻¹ ≤ Real.log p * om⁻¹ := by
    calc
      (P - P⁻¹) / 2 * O⁻¹ ≤
          (P - P⁻¹) / 2 * om⁻¹ :=
        mul_le_mul_of_nonpos_left homInv hLP0
      _ ≤ (p - p⁻¹) / 2 * om⁻¹ :=
        mul_le_mul_of_nonneg_right hLP (inv_nonneg.mpr hom.le)
      _ ≤ Real.log p * om⁻¹ :=
        mul_le_mul_of_nonneg_right hlogP (inv_nonneg.mpr hom.le)
  unfold tangentXLog
  dsimp only
  change smallBookXLower z ≤
    Real.log p * Real.exp (-Real.log om) + Real.log om
  rw [Real.exp_neg, Real.exp_log hom]
  dsimp [smallBookXLower, P, O]
  linarith

private def smallBookValueNumerator (z : ℝ) : ℝ :=
  588200769464 * z ^ 13 + 1385927601520 * z ^ 12 -
    2375930806711 * z ^ 11 - 3427520397455 * z ^ 10 +
    868044290113 * z ^ 9 - 13927091322529 * z ^ 8 -
    9103451382830 * z ^ 7 + 5299630764500 * z ^ 6 -
    9227594889000 * z ^ 5 - 2615815545000 * z ^ 4 +
    3167570880000 * z ^ 3 - 1015531680000 * z ^ 2 +
    74141760000 * z - 58800000

private lemma small_book_value_numerator_nonneg {z : ℝ}
    (hz : z ∈ Set.Icc (1 / 50 : ℝ) (1 / 10)) :
    0 ≤ smallBookValueNumerator z := by
  let u : ℝ := (50 * z - 1) / 4
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have h := KernelBounds.bernstein_sum_nonneg 13
    [4095381691643235541742238097148667,
      64938146987803583067012935724011355,
      438892138332607471487441736902710650,
      1719051325177416460594457584865195250,
      4409075483372580701866491621434315625,
      7867834381767896218270646803388840625,
      10071052439910314445410526767996437500,
      9352560849076336712262722878857187500,
      6271500451469715935894435814073828125,
      2968471612392110094913589189267578125,
      943717664993993570052257116816406250,
      181651095265817635788040802050781250,
      16244638623456544603705339599609375,
      70787726943900554071614990234375] hu
  have hid :
      smallBookValueNumerator z =
        (∑ i ∈ Finset.range 14,
          (([4095381691643235541742238097148667,
              64938146987803583067012935724011355,
              438892138332607471487441736902710650,
              1719051325177416460594457584865195250,
              4409075483372580701866491621434315625,
              7867834381767896218270646803388840625,
              10071052439910314445410526767996437500,
              9352560849076336712262722878857187500,
              6271500451469715935894435814073828125,
              2968471612392110094913589189267578125,
              943717664993993570052257116816406250,
              181651095265817635788040802050781250,
              16244638623456544603705339599609375,
              70787726943900554071614990234375].getD i 0 : ℕ) : ℝ) *
            u ^ i * (1 - u) ^ (13 - i)) /
          3927612304687500000000000 := by
    dsimp [smallBookValueNumerator, u]
    norm_num [Finset.sum_range_succ]
    ring
  rw [hid]
  exact div_nonneg h (by norm_num)

private lemma small_book_value_rational_margin {z : ℝ}
    (hz : z ∈ Set.Icc (1 / 50 : ℝ) (1 / 10)) :
    (1 / 10000 : ℝ) ≤ smallBookValueLower z := by
  have hnum := small_book_value_numerator_nonneg hz
  have hzOne : 0 < z + 1 := by linarith [hz.1]
  have hzTwo : 0 < z + 2 := by linarith [hz.1]
  have hfive : 0 < 5 - 11 * z := by nlinarith [hz.2]
  have hquad : 0 < 49 * z ^ 2 - 36 * z + 28 := by
    nlinarith [sq_nonneg z, hz.2]
  have hOne : 1 + z ≠ 0 := by linarith [hzOne]
  have hfive' : 5 - z * 11 ≠ 0 := by nlinarith [hfive]
  have hquad' : 28 - z * 36 + z ^ 2 * 49 ≠ 0 := by
    nlinarith [hquad]
  have hden :
      0 < 2100000000 * (z + 1) * (z + 2) *
        (5 - 11 * z) * (49 * z ^ 2 - 36 * z + 28) := by
    positivity
  have hPeq :
      smallBookP z = (49 * z ^ 2 - 36 * z + 28) / 28 := by
    unfold smallBookP smallBookExpUpper
    ring
  have hPinv :
      (smallBookP z)⁻¹ =
        28 / (49 * z ^ 2 - 36 * z + 28) := by
    rw [hPeq]
    field_simp [hquad.ne']
  have hid :
      smallBookValueLower z - 1 / 10000 =
        smallBookValueNumerator z /
          (2100000000 * (z + 1) * (z + 2) *
            (5 - 11 * z) * (49 * z ^ 2 - 36 * z + 28)) := by
    rw [eq_div_iff hden.ne']
    dsimp [smallBookValueLower, smallBookRamseyLower,
      smallBookXLower]
    rw [hPinv, hPeq]
    dsimp [smallBookO, smallBookExpUpper,
      smallBookYLower, smallBookLogUpper, smallBookCorrectionUpper,
      smallBookExpLower, smallBookValueNumerator]
    field_simp [hOne, hzOne.ne', hzTwo.ne', hfive.ne', hfive',
      hquad.ne', hquad']
    ring_nf
    field_simp [hquad']
    ring
  rw [← sub_nonneg, hid]
  exact div_nonneg hnum hden.le

/-- A uniform direct lower bound for the small-book comparison throughout
all three tangent rounds. -/
lemma tangent_small_book_lower
    {β₀ β₁ z : ℝ}
    (hβ₀ : β₀ ∈ Set.Icc 0 (2 / 25))
    (hβ₁ : β₁ ∈ Set.Icc (3 / 100) (2 / 25))
    (hz : z ∈ Set.Icc (1 / 50) (1 / 10)) :
    (1 / 10000 : ℝ) ≤ tangentSmallBookMargin β₀ β₁ z := by
  have hz' : z ∈ Set.Icc (0 : ℝ) (1 / 10) :=
    ⟨le_trans (by norm_num) hz.1, hz.2⟩
  have hentropy := Real.le_log_one_add_of_nonneg hz'.1
  have hentropy' :
      (1 + z) * (2 * z / (z + 2)) ≤
        (1 + z) * Real.log (1 + z) :=
    mul_le_mul_of_nonneg_left hentropy (by linarith [hz'.1])
  have hramsey := small_book_ramsey_lower hβ₁ hz'
  have hx := small_book_x_lower hβ₁ hz'
  have hy := small_book_y_lower hβ₀ hz'
  have hzy :
      z * smallBookYLower z ≤
        z * tangentSmallYLogOverZ β₀ z :=
    mul_le_mul_of_nonneg_left hy hz'.1
  have hbracket :
      (smallBookXLower z - z ^ 2 + z * smallBookYLower z) / 2 ≤
        (tangentXLog β₁ z - z ^ 2 +
          z * tangentSmallYLogOverZ β₀ z) / 2 := by
    linarith
  have hrat := small_book_value_rational_margin hz
  unfold tangentSmallBookMargin tangentCleanBookMargin
  dsimp [smallBookValueLower] at hrat
  linarith

private lemma correction_slope_deriv_upper_medium {β z : ℝ}
    (hβ : β ∈ Set.Icc 0 (2 / 25))
    (hz : z ∈ Set.Icc 0 (2 / 5)) :
    tangentCorrectionSlopeDeriv β z ≤ 2 / 3 := by
  let D : ℝ :=
    (2 * β + 12 / 25 * z -
        (-(1 / 4) + 2 * β * z + 6 / 25 * z ^ 2)) -
      (-(1 / 4) + 2 * β * z + 6 / 25 * z ^ 2 -
        (-(1 / 4) * z + β * z ^ 2 + 2 / 25 * z ^ 3))
  have hDid :
      D = 1 / 2 + β * (2 - 4 * z + z ^ 2) +
        23 / 100 * z - 12 / 25 * z ^ 2 + 2 / 25 * z ^ 3 := by
    dsimp [D]
    ring
  have hz2 : z ^ 2 ≤ (4 / 25 : ℝ) := by
    nlinarith [mul_nonneg hz.1 (sub_nonneg.mpr hz.2)]
  have hβz : β * z ≤ (4 / 125 : ℝ) :=
    calc
      β * z ≤ (2 / 25 : ℝ) * (2 / 5) :=
        mul_le_mul hβ.2 hz.2 hz.1 (by norm_num)
      _ = 4 / 125 := by norm_num
  have hD0 : 0 ≤ D := by
    have hbase :
        0 ≤ 1 / 2 - 4 * β * z - 12 / 25 * z ^ 2 := by
      nlinarith
    have hrest :
        0 ≤ 2 * β + β * z ^ 2 +
          23 / 100 * z + 2 / 25 * z ^ 3 := by
      exact add_nonneg
        (add_nonneg
          (add_nonneg (mul_nonneg (by norm_num) hβ.1)
            (mul_nonneg hβ.1 (sq_nonneg z)))
          (mul_nonneg (by norm_num) hz.1))
        (mul_nonneg (by norm_num)
          (mul_nonneg (sq_nonneg z) hz.1))
    rw [hDid]
    nlinarith
  have hcoef : 0 ≤ 2 - 4 * z + z ^ 2 := by
    nlinarith [sq_nonneg (z - 2)]
  have hβcoef :
      β * (2 - 4 * z + z ^ 2) ≤
        (2 / 25 : ℝ) * (2 - 4 * z + z ^ 2) :=
    mul_le_mul_of_nonneg_right hβ.2 hcoef
  have hz3 :
      z ^ 3 ≤ (2 / 5 : ℝ) * z ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg z) (sub_nonneg.mpr hz.2)]
  have hz3' :
      (2 / 25 : ℝ) * z ^ 3 ≤ (4 / 125) * z ^ 2 :=
    by nlinarith
  have hD : D ≤ 2 / 3 := by
    calc
      D = 1 / 2 + β * (2 - 4 * z + z ^ 2) +
          23 / 100 * z - 12 / 25 * z ^ 2 + 2 / 25 * z ^ 3 :=
        hDid
      _ ≤ 1 / 2 + (2 / 25) * (2 - 4 * z + z ^ 2) +
          23 / 100 * z - 12 / 25 * z ^ 2 + 2 / 25 * z ^ 3 := by
        linarith
      _ ≤ 2 / 3 := by
        nlinarith [sq_nonneg z, mul_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 100) hz.1]
  have he : Real.exp (-z) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith [hz.1])
  unfold tangentCorrectionSlopeDeriv
  dsimp only
  calc
    D * Real.exp (-z) ≤ D * 1 :=
      mul_le_mul_of_nonneg_left he hD0
    _ = D := mul_one D
    _ ≤ 2 / 3 := hD

private lemma tangent_blue_prime_nonneg_medium {β z : ℝ}
    (hβ : β ∈ Set.Icc 0 (2 / 25))
    (hz : z ∈ Set.Icc 0 (2 / 5)) :
    0 ≤ tangentBluePrime β z := by
  have hd := correction_slope_deriv_upper_medium hβ hz
  have hzplus : 0 < 1 + z := by linarith [hz.1]
  have hinv : (1 + z)⁻¹ ≤ 1 :=
    (inv_le_one₀ hzplus).mpr (by linarith [hz.1])
  let F : ℝ :=
    1 - z * ((1 + z)⁻¹ + tangentCorrectionSlopeDeriv β z)
  have hsum :
      (1 + z)⁻¹ + tangentCorrectionSlopeDeriv β z ≤ 5 / 3 := by
    linarith
  have hF : 0 ≤ F := by
    have hmul :
        z * ((1 + z)⁻¹ + tangentCorrectionSlopeDeriv β z) ≤
          z * (5 / 3) :=
      mul_le_mul_of_nonneg_left hsum hz.1
    have hzmul : z * (5 / 3 : ℝ) ≤ 2 / 3 := by
      linarith [hz.2]
    dsimp [F]
    linarith
  change
    0 ≤ Real.exp
      (-Real.log (1 + z) - tangentCorrectionSlope β z) * F
  positivity

private lemma tangent_medium_domain {β z : ℝ}
    (hβ : β ∈ Set.Icc 0 (2 / 25))
    (hz : z ∈ Set.Icc 0 (2 / 5)) :
    0 < 1 - tangentBlue β z ∧
      0 < 1 - optimizationM z ∧
      0 < 1 + z := by
  have hz1 : z ≤ 1 := by nlinarith [hz.2]
  exact ⟨sub_pos.mpr (tangentBlue_lt_one hβ.1 hz.1 hz1),
    sub_pos.mpr (optimizationM_lt_one_of_Icc hz.1 hz1),
    by linarith [hz.1]⟩

private lemma tangent_xlog_prime_nonpos_medium {β z : ℝ}
    (hβ : β ∈ Set.Icc 0 (2 / 25))
    (hz : z ∈ Set.Icc 0 (2 / 5)) :
    tangentXLogPrime β z ≤ 0 := by
  have hd := tangent_medium_domain hβ hz
  let p : ℝ := 1 - tangentBlue β z
  let om : ℝ := 1 - optimizationM z
  have hp : 0 < p := hd.1
  have hom : 0 < om := hd.2.1
  have hblue : 0 ≤ tangentBlue β z := by
    unfold tangentBlue
    exact mul_nonneg hz.1 (Real.exp_pos _).le
  have hp1 : p ≤ 1 := by
    dsimp [p]
    linarith
  have hlogp : Real.log p ≤ 0 := Real.log_nonpos hp.le hp1
  have hbp : 0 ≤ tangentBluePrime β z :=
    tangent_blue_prime_nonneg_medium hβ hz
  have hmu : 0 ≤ tangentMuPrime z := by
    unfold tangentMuPrime
    exact mul_nonneg (by linarith [hz.2]) (Real.exp_pos _).le
  have hfirst :
      -tangentBluePrime β z * p⁻¹ * om⁻¹ ≤ 0 := by
    have : 0 ≤ tangentBluePrime β z * p⁻¹ * om⁻¹ := by positivity
    linarith
  have hsecond :
      Real.log p * tangentMuPrime z * (om⁻¹) ^ 2 ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg hlogp hmu) (sq_nonneg _)
  have hthird : -tangentMuPrime z * om⁻¹ ≤ 0 := by
    have : 0 ≤ tangentMuPrime z * om⁻¹ := by positivity
    linarith
  unfold tangentXLogPrime
  dsimp only
  dsimp [p, om] at hfirst hsecond hthird
  linarith

/-- On the range containing all three plateau intervals, the logarithm of
the optimized `X`-coordinate decreases with `z`. -/
lemma tangent_xlog_antitone_medium {β : ℝ}
    (hβ : β ∈ Set.Icc 0 (2 / 25)) :
    AntitoneOn (tangentXLog β) (Set.Icc 0 (2 / 5)) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos
    (convex_Icc (0 : ℝ) (2 / 5))
  · intro z hz
    have hd := tangent_medium_domain hβ hz
    exact (hasDerivAt_tangentXLog β hd.1 hd.2.1 hd.2.2.ne').continuousAt.continuousWithinAt
  · intro z hz
    have hzIoo : z ∈ Set.Ioo (0 : ℝ) (2 / 5) := by
      simpa [interior_Icc] using hz
    have hz' : z ∈ Set.Icc (0 : ℝ) (2 / 5) :=
      ⟨hzIoo.1.le, hzIoo.2.le⟩
    have hd := tangent_medium_domain hβ hz'
    exact (hasDerivAt_tangentXLog β hd.1 hd.2.1 hd.2.2.ne').hasDerivWithinAt
  · intro z hz
    apply tangent_xlog_prime_nonpos_medium hβ
    have hzIoo : z ∈ Set.Ioo (0 : ℝ) (2 / 5) := by
      simpa [interior_Icc] using hz
    exact ⟨hzIoo.1.le, hzIoo.2.le⟩

def mediumExpNegLower (z : ℝ) : ℝ :=
  KernelBounds.expNegTaylor9 z - KernelBounds.expNegError10 z

def mediumExpNegUpper (z : ℝ) : ℝ :=
  KernelBounds.expNegTaylor9 z + KernelBounds.expNegError10 z

private lemma medium_exp_neg_bounds {z : ℝ}
    (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    mediumExpNegLower z ≤ Real.exp (-z) ∧
      Real.exp (-z) ≤ mediumExpNegUpper z := by
  have h := KernelBounds.exp_neg_approx hz
  have ha := abs_le.mp h
  dsimp [mediumExpNegLower, mediumExpNegUpper]
  constructor <;> linarith

def mediumLogLowerThree (x : ℝ) : ℝ :=
  let y := (x - 1) / (x + 1)
  2 * (y + y ^ 3 / 3 + y ^ 5 / 5)

private lemma medium_log_lower_three {x : ℝ} (hx : 1 ≤ x) :
    mediumLogLowerThree x ≤ Real.log x := by
  let y : ℝ := (x - 1) / (x + 1)
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hxp1 : 0 < x + 1 := by positivity
  have hy0 : 0 ≤ y := div_nonneg (sub_nonneg.mpr hx) hxp1.le
  have hy1 : y < 1 := by
    rw [div_lt_one hxp1]
    linarith
  have hyabs : |y| < 1 := by
    simpa [abs_of_nonneg hy0] using hy1
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one hyabs
  have hpartial :=
    hs.summable.sum_le_tsum (Finset.range 3) (by
      intro i hi
      positivity)
  rw [hs.tsum_eq] at hpartial
  have hlog :
      Real.log x = Real.log (1 + y) - Real.log (1 - y) := by
    rw [← Real.log_div]
    · congr 1
      dsimp [y]
      field_simp
      ring
    · dsimp [y]
      field_simp
      linarith
    · dsimp [y]
      field_simp
      linarith
  rw [hlog]
  norm_num [Finset.sum_range_succ, mediumLogLowerThree, y] at hpartial ⊢
  nlinarith

def mediumLogUpperSix (x : ℝ) : ℝ :=
  let y := (x - 1) / (x + 1)
  2 * (y + y ^ 3 / 3 + y ^ 5 / 5 + y ^ 7 / 7 +
    y ^ 9 / 9 + y ^ 11 / 11 + y ^ 13 / (1 - y ^ 2))

private lemma medium_log_upper_six {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ mediumLogUpperSix x := by
  let y : ℝ := (x - 1) / (x + 1)
  have hxp1 : 0 < x + 1 := by positivity
  have hy0 : 0 ≤ y := div_nonneg (sub_nonneg.mpr hx) hxp1.le
  have hy1 : y < 1 := by
    rw [div_lt_one hxp1]
    linarith
  have h := Real.log_div_le_sum_range_add hy0 hy1 6
  have hratio : (1 + y) / (1 - y) = x := by
    dsimp [y]
    field_simp
    ring
  rw [hratio] at h
  norm_num [Finset.sum_range_succ, mediumLogUpperSix, y] at h ⊢
  linarith

def mediumLogLowerBelow (x : ℝ) : ℝ :=
  let y := (1 - x) / (1 + x)
  (-2) * (y + y ^ 3 / 3 + y ^ 5 / (1 - y ^ 2))

private lemma medium_log_lower_below {x : ℝ}
    (hx : 0 < x) (hx1 : x ≤ 1) :
    mediumLogLowerBelow x ≤ Real.log x := by
  let y : ℝ := (1 - x) / (1 + x)
  have hxplus : 0 < 1 + x := by linarith
  have hy0 : 0 ≤ y := div_nonneg (sub_nonneg.mpr hx1) hxplus.le
  have hy1 : y < 1 := by
    rw [div_lt_one hxplus]
    linarith
  have h := Real.log_div_le_sum_range_add hy0 hy1 2
  have hratio : (1 + y) / (1 - y) = x⁻¹ := by
    dsimp [y]
    field_simp [hx.ne', hxplus.ne']
    ring
  rw [hratio, Real.log_inv] at h
  norm_num [Finset.sum_range_succ, mediumLogLowerBelow, y] at h ⊢
  linarith

def mediumLogUpperBelow (x : ℝ) : ℝ :=
  -mediumLogLowerThree x⁻¹

private lemma medium_log_upper_below {x : ℝ}
    (hx : 0 < x) (hx1 : x ≤ 1) :
    Real.log x ≤ mediumLogUpperBelow x := by
  have hinv : (1 : ℝ) ≤ x⁻¹ := (one_le_inv₀ hx).mpr hx1
  have h := medium_log_lower_three hinv
  rw [Real.log_inv] at h
  dsimp [mediumLogUpperBelow]
  linarith

def mediumCorrectionPolynomial (β z : ℝ) : ℝ :=
  -(1 / 4) + 2 * β * z + 6 / 25 * z ^ 2 -
    (-(1 / 4) * z + β * z ^ 2 + 2 / 25 * z ^ 3)

private def mediumBlueLower (β z : ℝ) : ℝ :=
  let q :=
    mediumLogUpperSix (1 + z) +
      mediumCorrectionPolynomial β z * mediumExpNegLower z
  z * mediumExpNegLower q

private lemma medium_blue_lower {β z : ℝ}
    (hz : z ∈ Set.Icc (0 : ℝ) 1)
    (hP : mediumCorrectionPolynomial β z ≤ 0)
    (hq : mediumLogUpperSix (1 + z) +
        mediumCorrectionPolynomial β z * mediumExpNegLower z ∈
      Set.Icc (0 : ℝ) 1) :
    mediumBlueLower β z ≤ tangentBlue β z := by
  let q : ℝ :=
    mediumLogUpperSix (1 + z) +
      mediumCorrectionPolynomial β z * mediumExpNegLower z
  have hez := (medium_exp_neg_bounds hz).1
  have hcorr :
      tangentCorrectionSlope β z ≤
        mediumCorrectionPolynomial β z * mediumExpNegLower z := by
    unfold tangentCorrectionSlope
    change
      mediumCorrectionPolynomial β z * Real.exp (-z) ≤
        mediumCorrectionPolynomial β z * mediumExpNegLower z
    exact mul_le_mul_of_nonpos_left hez hP
  have hlog := medium_log_upper_six
    (show (1 : ℝ) ≤ 1 + z by linarith [hz.1])
  have harg :
      -q ≤ -Real.log (1 + z) - tangentCorrectionSlope β z := by
    dsimp [q]
    linarith
  have hexp :
      Real.exp (-q) ≤
        Real.exp (-Real.log (1 + z) - tangentCorrectionSlope β z) :=
    Real.exp_le_exp.mpr harg
  have hqexp := (medium_exp_neg_bounds hq).1
  unfold tangentBlue mediumBlueLower
  dsimp only
  exact mul_le_mul_of_nonneg_left (hqexp.trans hexp) hz.1

private def mediumBlueUpper (β z : ℝ) : ℝ :=
  let q :=
    mediumLogLowerThree (1 + z) +
      mediumCorrectionPolynomial β z * mediumExpNegUpper z
  z * mediumExpNegUpper q

private lemma medium_blue_upper {β z : ℝ}
    (hz : z ∈ Set.Icc (0 : ℝ) 1)
    (hP : mediumCorrectionPolynomial β z ≤ 0)
    (hq : mediumLogLowerThree (1 + z) +
        mediumCorrectionPolynomial β z * mediumExpNegUpper z ∈
      Set.Icc (0 : ℝ) 1) :
    tangentBlue β z ≤ mediumBlueUpper β z := by
  let q : ℝ :=
    mediumLogLowerThree (1 + z) +
      mediumCorrectionPolynomial β z * mediumExpNegUpper z
  have hez := (medium_exp_neg_bounds hz).2
  have hcorr :
      mediumCorrectionPolynomial β z * mediumExpNegUpper z ≤
        tangentCorrectionSlope β z := by
    unfold tangentCorrectionSlope
    change
      mediumCorrectionPolynomial β z * mediumExpNegUpper z ≤
        mediumCorrectionPolynomial β z * Real.exp (-z)
    exact mul_le_mul_of_nonpos_left hez hP
  have hlog := medium_log_lower_three
    (show (1 : ℝ) ≤ 1 + z by linarith [hz.1])
  have harg :
      -Real.log (1 + z) - tangentCorrectionSlope β z ≤ -q := by
    dsimp [q]
    linarith
  have hexp :
      Real.exp (-Real.log (1 + z) - tangentCorrectionSlope β z) ≤
        Real.exp (-q) :=
    Real.exp_le_exp.mpr harg
  have hqexp := (medium_exp_neg_bounds hq).2
  unfold tangentBlue mediumBlueUpper
  dsimp only
  exact mul_le_mul_of_nonneg_left (hexp.trans hqexp) hz.1

private lemma medium_mu_lower {z M : ℝ}
    (hz : z ∈ Set.Icc (0 : ℝ) 1)
    (hM : M ≤ z * mediumExpNegLower z) :
    M ≤ optimizationM z := by
  unfold optimizationM
  exact hM.trans (mul_le_mul_of_nonneg_left
    (medium_exp_neg_bounds hz).1 hz.1)

private lemma medium_mu_upper {z M : ℝ}
    (hz : z ∈ Set.Icc (0 : ℝ) 1)
    (hM : z * mediumExpNegUpper z ≤ M) :
    optimizationM z ≤ M := by
  unfold optimizationM
  exact (mul_le_mul_of_nonneg_left
    (medium_exp_neg_bounds hz).2 hz.1).trans hM

private lemma tangent_xlog_upper_of_lower_bounds
    {β z B M : ℝ}
    (hβ : 0 ≤ β) (hz : z ∈ Set.Icc (0 : ℝ) 1)
    (hB0 : 0 ≤ B) (hB : B ≤ tangentBlue β z)
    (hM0 : 0 ≤ M) (hM : M ≤ optimizationM z)
    (hB1 : B < 1) (hM1 : M < 1) :
    tangentXLog β z ≤
      mediumLogUpperBelow (1 - B) * (1 - M)⁻¹ +
        mediumLogUpperBelow (1 - M) := by
  let p : ℝ := 1 - tangentBlue β z
  let om : ℝ := 1 - optimizationM z
  let pB : ℝ := 1 - B
  let omM : ℝ := 1 - M
  have hp : 0 < p :=
    sub_pos.mpr (tangentBlue_lt_one hβ hz.1 hz.2)
  have hom : 0 < om :=
    sub_pos.mpr (optimizationM_lt_one_of_Icc hz.1 hz.2)
  have hpB : 0 < pB := by dsimp [pB]; linarith
  have homM : 0 < omM := by dsimp [omM]; linarith
  have hp_le : p ≤ pB := by dsimp [p, pB]; linarith
  have hom_le : om ≤ omM := by dsimp [om, omM]; linarith
  have hlogp :
      Real.log p ≤ mediumLogUpperBelow pB := by
    have hmono := Real.strictMonoOn_log.monotoneOn hp hpB
      hp_le
    exact hmono.trans (medium_log_upper_below hpB (by
      dsimp [pB]
      linarith))
  have hlogom :
      Real.log om ≤ mediumLogUpperBelow omM := by
    have hmono := Real.strictMonoOn_log.monotoneOn hom homM
      hom_le
    exact hmono.trans (medium_log_upper_below homM (by
      dsimp [omM]
      linarith))
  have hubp : mediumLogUpperBelow pB ≤ 0 :=
    by
      have hpBinv : (1 : ℝ) ≤ pB⁻¹ :=
        (one_le_inv₀ hpB).mpr (by
          dsimp [pB]
          linarith)
      let y : ℝ := (pB⁻¹ - 1) / (pB⁻¹ + 1)
      have hy : 0 ≤ y := by
        dsimp [y]
        positivity
      have hnonneg : 0 ≤ mediumLogLowerThree pB⁻¹ := by
        dsimp [mediumLogLowerThree, y]
        positivity
      dsimp [mediumLogUpperBelow]
      linarith
  have hinv : omM⁻¹ ≤ om⁻¹ :=
    (inv_le_inv₀ homM hom).mpr hom_le
  have hfirst :
      Real.log p * om⁻¹ ≤
        mediumLogUpperBelow pB * omM⁻¹ := by
    calc
      Real.log p * om⁻¹ ≤ mediumLogUpperBelow pB * om⁻¹ :=
        mul_le_mul_of_nonneg_right hlogp (inv_nonneg.mpr hom.le)
      _ ≤ mediumLogUpperBelow pB * omM⁻¹ :=
        mul_le_mul_of_nonpos_left hinv hubp
  unfold tangentXLog
  dsimp only
  rw [Real.exp_neg, Real.exp_log hom]
  dsimp [p, om, pB, omM] at hfirst hlogom ⊢
  linarith

private lemma tangent_xlog_lower_of_upper_bounds
    {β z B M : ℝ}
    (hβ : 0 ≤ β) (hz : z ∈ Set.Icc (0 : ℝ) 1)
    (hB0 : 0 ≤ B) (hM0 : 0 ≤ M)
    (hB : tangentBlue β z ≤ B)
    (hM : optimizationM z ≤ M)
    (hB1 : B < 1) (hM1 : M < 1) :
    mediumLogLowerBelow (1 - B) * (1 - M)⁻¹ +
        mediumLogLowerBelow (1 - M) ≤
      tangentXLog β z := by
  let p : ℝ := 1 - tangentBlue β z
  let om : ℝ := 1 - optimizationM z
  let pB : ℝ := 1 - B
  let omM : ℝ := 1 - M
  have hp : 0 < p :=
    sub_pos.mpr (tangentBlue_lt_one hβ hz.1 hz.2)
  have hom : 0 < om :=
    sub_pos.mpr (optimizationM_lt_one_of_Icc hz.1 hz.2)
  have hpB : 0 < pB := by dsimp [pB]; linarith
  have homM : 0 < omM := by dsimp [omM]; linarith
  have hpB_le : pB ≤ p := by dsimp [p, pB]; linarith
  have homM_le : omM ≤ om := by dsimp [om, omM]; linarith
  have hlogp :
      mediumLogLowerBelow pB ≤ Real.log p := by
    exact (medium_log_lower_below hpB (by
      dsimp [pB]
      linarith)).trans
        (Real.strictMonoOn_log.monotoneOn hpB hp hpB_le)
  have hlogom :
      mediumLogLowerBelow omM ≤ Real.log om := by
    exact (medium_log_lower_below homM (by
      dsimp [omM]
      linarith)).trans
        (Real.strictMonoOn_log.monotoneOn homM hom homM_le)
  have hlbp : mediumLogLowerBelow pB ≤ 0 :=
    (medium_log_lower_below hpB (by
      dsimp [pB]
      linarith)).trans (Real.log_nonpos hpB.le (by
        dsimp [pB]
        linarith))
  have hinv : om⁻¹ ≤ omM⁻¹ :=
    (inv_le_inv₀ hom homM).mpr homM_le
  have hfirst :
      mediumLogLowerBelow pB * omM⁻¹ ≤
        Real.log p * om⁻¹ := by
    calc
      mediumLogLowerBelow pB * omM⁻¹ ≤
          mediumLogLowerBelow pB * om⁻¹ :=
        mul_le_mul_of_nonpos_left hinv hlbp
      _ ≤ Real.log p * om⁻¹ :=
        mul_le_mul_of_nonneg_right hlogp (inv_nonneg.mpr hom.le)
  unfold tangentXLog
  dsimp only
  rw [Real.exp_neg, Real.exp_log hom]
  dsimp [p, om, pB, omM] at hfirst hlogom ⊢
  linarith

/-!
The following rational bounds are designed for the nonconstant coordinate
comparisons. They deliberately keep only three terms of the positive
exponential series; this is already sharp enough for the tangent witnesses
and keeps the exact polynomial certificates reasonably small.
-/

def tangentCoordExpLower (z : ℝ) : ℝ :=
  1 - z + z ^ 2 / 2 - z ^ 3 / 6

def tangentCoordALogExpLower (z : ℝ) : ℝ :=
  1 - z + z ^ 2 / 2 - z ^ 3 / 6 + z ^ 4 / 24 -
    z ^ 5 / 120 + z ^ 6 / 720 - z ^ 7 / 5040

def tangentCoordLogUpper (x : ℝ) : ℝ :=
  let s := (2 - x) / 2
  693147181 / 1000000000 -
    (s + s ^ 2 / 2 + s ^ 3 / 3 + s ^ 4 / 4 +
      s ^ 5 / 5 + s ^ 6 / 6)

def tangentCoordLogUpperBelow (x : ℝ) : ℝ :=
  let y := 1 - x
  (-(y + y ^ 2 / 2 + y ^ 3 / 3 + y ^ 4 / 4 + y ^ 5 / 5))

def tangentCoordSlopeMagnitudeLower (β z : ℝ) : ℝ :=
  -mediumCorrectionPolynomial β z * tangentCoordExpLower z

def tangentCoordBlueLower (β z : ℝ) : ℝ :=
  let q := tangentCoordSlopeMagnitudeLower β z
  z * (1 + z)⁻¹ * (1 + q + q ^ 2 / 2)

def tangentCoordMuLower (z : ℝ) : ℝ :=
  z * tangentCoordExpLower z

def tangentCoordXLogUpper (β z : ℝ) : ℝ :=
  let B := tangentCoordBlueLower β z
  let M := tangentCoordMuLower z
  tangentCoordLogUpperBelow (1 - B) * (1 - M)⁻¹ +
    tangentCoordLogUpperBelow (1 - M)

def tangentCoordALogLower (β t : ℝ) : ℝ :=
  let coefficient :=
    t ^ 2 *
      (1 / 4 + β + (4 / 25 - β) * t - (2 / 25) * t ^ 2)
  (-tangentCoordLogUpper (1 + t)) +
    coefficient * tangentCoordALogExpLower t

lemma tangent_coord_exp_lower_nonneg {z : ℝ}
    (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ tangentCoordExpLower z := by
  have h01 : 0 ≤ 1 - z := sub_nonneg.mpr hz.2
  have h23 : 0 ≤ z ^ 2 * (1 / 2 - z / 6) :=
    mul_nonneg (sq_nonneg z) (by nlinarith [hz.2])
  dsimp [tangentCoordExpLower]
  nlinarith

private lemma tangent_coord_exp_lower_le {z : ℝ}
    (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    tangentCoordExpLower z ≤ mediumExpNegLower z := by
  have h45 : 0 ≤ z ^ 4 * (1 / 24 - z / 120) :=
    mul_nonneg (pow_nonneg hz.1 4) (by nlinarith [hz.2])
  have h67 : 0 ≤ z ^ 6 * (1 / 720 - z / 5040) :=
    mul_nonneg (pow_nonneg hz.1 6) (by nlinarith [hz.2])
  have h89 :
      0 ≤ z ^ 8 *
        (1 / 40320 - z / 362880 -
          11 * z ^ 2 / 36288000) := by
    apply mul_nonneg (pow_nonneg hz.1 8)
    nlinarith [hz.2, sq_nonneg z,
      mul_nonneg hz.1 (sub_nonneg.mpr hz.2)]
  dsimp [tangentCoordExpLower, mediumExpNegLower,
    KernelBounds.expNegTaylor9, KernelBounds.expNegError10]
  norm_num [Nat.factorial]
  nlinarith

private lemma tangent_coord_alog_exp_lower_le {z : ℝ}
    (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    tangentCoordALogExpLower z ≤ mediumExpNegLower z := by
  have h89 :
      0 ≤ z ^ 8 *
        (1 / 40320 - z / 362880 -
          11 * z ^ 2 / 36288000) := by
    apply mul_nonneg (pow_nonneg hz.1 8)
    nlinarith [hz.2, sq_nonneg z,
      mul_nonneg hz.1 (sub_nonneg.mpr hz.2)]
  dsimp [tangentCoordALogExpLower, mediumExpNegLower,
    KernelBounds.expNegTaylor9, KernelBounds.expNegError10]
  norm_num [Nat.factorial]
  nlinarith

private lemma tangent_coord_log_upper {x : ℝ}
    (hx : x ∈ Set.Icc (1 : ℝ) 2) :
    Real.log x ≤ tangentCoordLogUpper x := by
  let s : ℝ := (2 - x) / 2
  have hs0 : 0 ≤ s := by dsimp [s]; linarith [hx.2]
  have hs1 : s < 1 := by dsimp [s]; linarith [hx.1]
  have hsabs : |s| < 1 := by
    simpa [abs_of_nonneg hs0] using hs1
  have hseries := Real.hasSum_pow_div_log_of_abs_lt_one hsabs
  have hpartial :=
    hseries.summable.sum_le_tsum (Finset.range 6) (by
      intro i hi
      positivity)
  rw [hseries.tsum_eq] at hpartial
  have hratio : 1 - s = x / 2 := by
    dsimp [s]
    ring
  rw [hratio] at hpartial
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx.1
  have hlog :
      Real.log x = Real.log 2 + Real.log (x / 2) := by
    calc
      Real.log x = Real.log (2 * (x / 2)) := by
        congr 1
        ring
      _ = Real.log 2 + Real.log (x / 2) :=
        Real.log_mul (by norm_num) (by positivity)
  have hlogTwo :
      Real.log 2 ≤ (693147181 / 1000000000 : ℝ) :=
    (le_of_lt Real.log_two_lt_d9).trans (by norm_num)
  rw [hlog]
  norm_num [Finset.sum_range_succ, tangentCoordLogUpper, s]
    at hpartial ⊢
  linarith

private lemma tangent_coord_log_upper_below {x : ℝ}
    (hx : 0 < x) (hx1 : x ≤ 1) :
    Real.log x ≤ tangentCoordLogUpperBelow x := by
  let y : ℝ := 1 - x
  have hy0 : 0 ≤ y := sub_nonneg.mpr hx1
  have hy1 : y < 1 := by dsimp [y]; linarith
  have hyabs : |y| < 1 := by
    simpa [abs_of_nonneg hy0] using hy1
  have hseries := Real.hasSum_pow_div_log_of_abs_lt_one hyabs
  have hpartial :=
    hseries.summable.sum_le_tsum (Finset.range 5) (by
      intro i hi
      positivity)
  rw [hseries.tsum_eq] at hpartial
  have harg : 1 - y = x := by dsimp [y]; ring
  rw [harg] at hpartial
  norm_num [Finset.sum_range_succ, tangentCoordLogUpperBelow, y]
    at hpartial ⊢
  linarith

lemma tangent_coord_blue_lower {β z : ℝ}
    (hz : z ∈ Set.Icc (0 : ℝ) 1)
    (hP : mediumCorrectionPolynomial β z ≤ 0) :
    tangentCoordBlueLower β z ≤ tangentBlue β z := by
  let q := tangentCoordSlopeMagnitudeLower β z
  have he := (tangent_coord_exp_lower_le hz).trans
    (medium_exp_neg_bounds hz).1
  have he0 := tangent_coord_exp_lower_nonneg hz
  have hq0 : 0 ≤ q := by
    dsimp [q, tangentCoordSlopeMagnitudeLower]
    exact mul_nonneg (neg_nonneg.mpr hP) he0
  have hq :
      q ≤ -mediumCorrectionPolynomial β z * Real.exp (-z) := by
    dsimp [q, tangentCoordSlopeMagnitudeLower,
      tangentCoordExpLower]
    exact mul_le_mul_of_nonneg_left he (neg_nonneg.mpr hP)
  have hseries := Real.sum_le_exp_of_nonneg hq0 3
  norm_num [Finset.sum_range_succ, Nat.factorial] at hseries
  have hexp :
      1 + q + q ^ 2 / 2 ≤
        Real.exp
          (-mediumCorrectionPolynomial β z * Real.exp (-z)) :=
    hseries.trans (Real.exp_le_exp.mpr hq)
  have hzplus : 0 < 1 + z := by linarith [hz.1]
  have hfactor : 0 ≤ z * (1 + z)⁻¹ :=
    mul_nonneg hz.1 (inv_nonneg.mpr hzplus.le)
  unfold tangentBlue tangentCoordBlueLower
  dsimp only [q]
  rw [show
      -Real.log (1 + z) - tangentCorrectionSlope β z =
        -Real.log (1 + z) +
          (-mediumCorrectionPolynomial β z * Real.exp (-z)) by
      unfold tangentCorrectionSlope mediumCorrectionPolynomial
      ring,
    Real.exp_add, Real.exp_neg, Real.exp_log hzplus]
  nlinarith [mul_le_mul_of_nonneg_left hexp hfactor]

lemma tangent_coord_xlog_le {β z : ℝ}
    (hβ : 0 ≤ β) (hz : z ∈ Set.Icc (0 : ℝ) 1)
    (hP : mediumCorrectionPolynomial β z ≤ 0)
    (hB0 : 0 ≤ tangentCoordBlueLower β z)
    (hB1 : tangentCoordBlueLower β z < 1)
    (hM0 : 0 ≤ tangentCoordMuLower z)
    (hM1 : tangentCoordMuLower z < 1) :
    tangentXLog β z ≤ tangentCoordXLogUpper β z := by
  have hB := tangent_coord_blue_lower hz hP
  have hMpoly :
      tangentCoordMuLower z ≤ z * mediumExpNegLower z := by
    unfold tangentCoordMuLower
    exact mul_le_mul_of_nonneg_left
      (tangent_coord_exp_lower_le hz) hz.1
  have hM := medium_mu_lower hz hMpoly
  let p : ℝ := 1 - tangentBlue β z
  let om : ℝ := 1 - optimizationM z
  let pB : ℝ := 1 - tangentCoordBlueLower β z
  let omM : ℝ := 1 - tangentCoordMuLower z
  have hp : 0 < p :=
    sub_pos.mpr (tangentBlue_lt_one hβ hz.1 hz.2)
  have hom : 0 < om :=
    sub_pos.mpr (optimizationM_lt_one_of_Icc hz.1 hz.2)
  have hpB : 0 < pB := by dsimp [pB]; linarith
  have homM : 0 < omM := by dsimp [omM]; linarith
  have hp_le : p ≤ pB := by dsimp [p, pB]; linarith
  have hom_le : om ≤ omM := by dsimp [om, omM]; linarith
  have hlogp :
      Real.log p ≤ tangentCoordLogUpperBelow pB := by
    exact (Real.strictMonoOn_log.monotoneOn hp hpB hp_le).trans
      (tangent_coord_log_upper_below hpB (by
        dsimp [pB]
        linarith))
  have hlogom :
      Real.log om ≤ tangentCoordLogUpperBelow omM := by
    exact (Real.strictMonoOn_log.monotoneOn hom homM hom_le).trans
      (tangent_coord_log_upper_below homM (by
        dsimp [omM]
        linarith))
  have hubp : tangentCoordLogUpperBelow pB ≤ 0 := by
    have hy0 : 0 ≤ 1 - pB := by
      simpa [pB] using hB0
    dsimp [tangentCoordLogUpperBelow]
    nlinarith [sq_nonneg (1 - pB),
      pow_nonneg hy0 3, pow_nonneg hy0 4, pow_nonneg hy0 5]
  have hinv : omM⁻¹ ≤ om⁻¹ :=
    (inv_le_inv₀ homM hom).mpr hom_le
  have hfirst :
      Real.log p * om⁻¹ ≤
        tangentCoordLogUpperBelow pB * omM⁻¹ := by
    calc
      Real.log p * om⁻¹ ≤
          tangentCoordLogUpperBelow pB * om⁻¹ :=
        mul_le_mul_of_nonneg_right hlogp (inv_nonneg.mpr hom.le)
      _ ≤ tangentCoordLogUpperBelow pB * omM⁻¹ :=
        mul_le_mul_of_nonpos_left hinv hubp
  unfold tangentXLog tangentCoordXLogUpper
  dsimp only
  rw [Real.exp_neg, Real.exp_log hom]
  dsimp [p, om, pB, omM] at hfirst hlogom ⊢
  linarith

lemma tangent_coord_alog_lower_le {β t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hcoefficient :
      0 ≤ t ^ 2 *
        (1 / 4 + β + (4 / 25 - β) * t -
          (2 / 25) * t ^ 2)) :
    tangentCoordALogLower β t ≤ tangentALog β t := by
  have hlog := tangent_coord_log_upper
    (show 1 + t ∈ Set.Icc (1 : ℝ) 2 by
      constructor <;> linarith [ht.1, ht.2])
  have hexp := (tangent_coord_alog_exp_lower_le ht).trans
    (medium_exp_neg_bounds ht).1
  have hmul := mul_le_mul_of_nonneg_left hexp hcoefficient
  unfold tangentALog tangentCoordALogLower
  dsimp only
  linarith

/-- The upper coordinate comparison on the third-round plateau. -/
lemma tangent_plateau_high_round3 :
    ∀ z ∈ Set.Icc (67 / 250 : ℝ) (3 / 8),
      tangentXLog (3 / 100) z ≤
        tangentALog (33 / 1000) (99 / 100) := by
  have hblueApprox := medium_blue_lower
    (β := (3 / 100 : ℝ)) (z := (67 / 250 : ℝ))
    (by norm_num)
    (by norm_num [mediumCorrectionPolynomial])
    (by norm_num [mediumLogUpperSix, mediumCorrectionPolynomial,
      mediumExpNegLower, KernelBounds.expNegTaylor9,
      KernelBounds.expNegError10, Nat.factorial])
  have hblue :
      (2375 / 10000 : ℝ) ≤ tangentBlue (3 / 100) (67 / 250) := by
    apply le_trans (b := mediumBlueLower (3 / 100) (67 / 250))
    · norm_num [mediumBlueLower, mediumLogUpperSix,
        mediumCorrectionPolynomial, mediumExpNegLower,
        KernelBounds.expNegTaylor9, KernelBounds.expNegError10,
        Nat.factorial]
    · exact hblueApprox
  have hmu :
      (2049 / 10000 : ℝ) ≤ optimizationM (67 / 250) := by
    apply medium_mu_lower (z := (67 / 250 : ℝ)) (by norm_num)
    norm_num [mediumExpNegLower, KernelBounds.expNegTaylor9,
      KernelBounds.expNegError10, Nat.factorial]
  have hx := tangent_xlog_upper_of_lower_bounds
    (β := (3 / 100 : ℝ)) (z := (67 / 250 : ℝ))
    (B := (2375 / 10000 : ℝ)) (M := (2049 / 10000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) hblue
    (by norm_num) hmu (by norm_num) (by norm_num)
  have hexp := (medium_exp_neg_bounds
    (z := (99 / 100 : ℝ)) (by norm_num)).1
  have hlog := medium_log_upper_six
    (x := (199 / 100 : ℝ)) (by norm_num)
  have hcoef :
      0 ≤ (99 / 100 : ℝ) ^ 2 *
        (1 / 4 + 33 / 1000 +
          (4 / 25 - 33 / 1000) * (99 / 100) -
          (2 / 25) * (99 / 100) ^ 2) := by
    norm_num
  have hterm :=
    mul_le_mul_of_nonneg_left hexp hcoef
  have hend :
      tangentXLog (3 / 100) (67 / 250) ≤
        tangentALog (33 / 1000) (99 / 100) := by
    unfold tangentALog
    norm_num [mediumLogUpperBelow, mediumLogLowerThree,
      mediumLogUpperSix, mediumExpNegLower,
      KernelBounds.expNegTaylor9, KernelBounds.expNegError10,
      Nat.factorial] at hx hlog hterm ⊢
    linarith
  intro z hz
  have hanti := tangent_xlog_antitone_medium
    (β := (3 / 100 : ℝ)) (by norm_num)
  have hzwide : z ∈ Set.Icc (0 : ℝ) (2 / 5) := by
    constructor <;> nlinarith [hz.1, hz.2]
  have hcut : (67 / 250 : ℝ) ∈ Set.Icc (0 : ℝ) (2 / 5) := by
    norm_num
  exact (hanti hcut hzwide hz.1).trans hend

/-- The upper coordinate comparison on the second-round plateau. -/
lemma tangent_plateau_high_round2 :
    ∀ z ∈ Set.Icc (67 / 250 : ℝ) (189 / 500),
      tangentXLog (33 / 1000) z ≤
        tangentALog (9 / 200) (99 / 100) := by
  have hblueApprox := medium_blue_lower
    (β := (33 / 1000 : ℝ)) (z := (67 / 250 : ℝ))
    (by norm_num)
    (by norm_num [mediumCorrectionPolynomial])
    (by norm_num [mediumLogUpperSix, mediumCorrectionPolynomial,
      mediumExpNegLower, KernelBounds.expNegTaylor9,
      KernelBounds.expNegError10, Nat.factorial])
  have hblue :
      (2373 / 10000 : ℝ) ≤ tangentBlue (33 / 1000) (67 / 250) := by
    apply le_trans (b := mediumBlueLower (33 / 1000) (67 / 250))
    · norm_num [mediumBlueLower, mediumLogUpperSix,
        mediumCorrectionPolynomial, mediumExpNegLower,
        KernelBounds.expNegTaylor9, KernelBounds.expNegError10,
        Nat.factorial]
    · exact hblueApprox
  have hmu :
      (2049 / 10000 : ℝ) ≤ optimizationM (67 / 250) := by
    apply medium_mu_lower (z := (67 / 250 : ℝ)) (by norm_num)
    norm_num [mediumExpNegLower, KernelBounds.expNegTaylor9,
      KernelBounds.expNegError10, Nat.factorial]
  have hx := tangent_xlog_upper_of_lower_bounds
    (β := (33 / 1000 : ℝ)) (z := (67 / 250 : ℝ))
    (B := (2373 / 10000 : ℝ)) (M := (2049 / 10000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) hblue
    (by norm_num) hmu (by norm_num) (by norm_num)
  have hexp := (medium_exp_neg_bounds
    (z := (99 / 100 : ℝ)) (by norm_num)).1
  have hlog := medium_log_upper_six
    (x := (199 / 100 : ℝ)) (by norm_num)
  have hcoef :
      0 ≤ (99 / 100 : ℝ) ^ 2 *
        (1 / 4 + 9 / 200 +
          (4 / 25 - 9 / 200) * (99 / 100) -
          (2 / 25) * (99 / 100) ^ 2) := by
    norm_num
  have hterm :=
    mul_le_mul_of_nonneg_left hexp hcoef
  have hend :
      tangentXLog (33 / 1000) (67 / 250) ≤
        tangentALog (9 / 200) (99 / 100) := by
    unfold tangentALog
    norm_num [mediumLogUpperBelow, mediumLogLowerThree,
      mediumLogUpperSix, mediumExpNegLower,
      KernelBounds.expNegTaylor9, KernelBounds.expNegError10,
      Nat.factorial] at hx hlog hterm ⊢
    linarith
  intro z hz
  have hanti := tangent_xlog_antitone_medium
    (β := (33 / 1000 : ℝ)) (by norm_num)
  have hzwide : z ∈ Set.Icc (0 : ℝ) (2 / 5) := by
    constructor <;> nlinarith [hz.1, hz.2]
  have hcut : (67 / 250 : ℝ) ∈ Set.Icc (0 : ℝ) (2 / 5) := by
    norm_num
  exact (hanti hcut hzwide hz.1).trans hend

/-- The upper coordinate comparison on the first-round plateau. -/
lemma tangent_plateau_high_round1 :
    ∀ z ∈ Set.Icc (269 / 1000 : ℝ) (387 / 1000),
      tangentXLog (9 / 200) z ≤
        tangentALog (2 / 25) (99 / 100) := by
  have hblueApprox := medium_blue_lower
    (β := (9 / 200 : ℝ)) (z := (269 / 1000 : ℝ))
    (by norm_num)
    (by norm_num [mediumCorrectionPolynomial])
    (by norm_num [mediumLogUpperSix, mediumCorrectionPolynomial,
      mediumExpNegLower, KernelBounds.expNegTaylor9,
      KernelBounds.expNegError10, Nat.factorial])
  have hblue :
      (2369 / 10000 : ℝ) ≤ tangentBlue (9 / 200) (269 / 1000) := by
    apply le_trans (b := mediumBlueLower (9 / 200) (269 / 1000))
    · norm_num [mediumBlueLower, mediumLogUpperSix,
        mediumCorrectionPolynomial, mediumExpNegLower,
        KernelBounds.expNegTaylor9, KernelBounds.expNegError10,
        Nat.factorial]
    · exact hblueApprox
  have hmu :
      (2055 / 10000 : ℝ) ≤ optimizationM (269 / 1000) := by
    apply medium_mu_lower (z := (269 / 1000 : ℝ)) (by norm_num)
    norm_num [mediumExpNegLower, KernelBounds.expNegTaylor9,
      KernelBounds.expNegError10, Nat.factorial]
  have hx := tangent_xlog_upper_of_lower_bounds
    (β := (9 / 200 : ℝ)) (z := (269 / 1000 : ℝ))
    (B := (2369 / 10000 : ℝ)) (M := (2055 / 10000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) hblue
    (by norm_num) hmu (by norm_num) (by norm_num)
  have hexp := (medium_exp_neg_bounds
    (z := (99 / 100 : ℝ)) (by norm_num)).1
  have hlog := medium_log_upper_six
    (x := (199 / 100 : ℝ)) (by norm_num)
  have hcoef :
      0 ≤ (99 / 100 : ℝ) ^ 2 *
        (1 / 4 + 2 / 25 +
          (4 / 25 - 2 / 25) * (99 / 100) -
          (2 / 25) * (99 / 100) ^ 2) := by
    norm_num
  have hterm :=
    mul_le_mul_of_nonneg_left hexp hcoef
  have hend :
      tangentXLog (9 / 200) (269 / 1000) ≤
        tangentALog (2 / 25) (99 / 100) := by
    unfold tangentALog
    norm_num [mediumLogUpperBelow, mediumLogLowerThree,
      mediumLogUpperSix, mediumExpNegLower,
      KernelBounds.expNegTaylor9, KernelBounds.expNegError10,
      Nat.factorial] at hx hlog hterm ⊢
    linarith
  intro z hz
  have hanti := tangent_xlog_antitone_medium
    (β := (9 / 200 : ℝ)) (by norm_num)
  have hzwide : z ∈ Set.Icc (0 : ℝ) (2 / 5) := by
    constructor <;> nlinarith [hz.1, hz.2]
  have hcut : (269 / 1000 : ℝ) ∈ Set.Icc (0 : ℝ) (2 / 5) := by
    norm_num
  exact (hanti hcut hzwide hz.1).trans hend

/-- The lower coordinate comparison on the third-round plateau. -/
lemma tangent_plateau_low_round3 :
    ∀ z ∈ Set.Icc (67 / 250 : ℝ) (3 / 8),
      tangentBLog (33 / 1000) (99 / 100) ≤
        tangentXLog (3 / 100) z := by
  have hblueApprox := medium_blue_upper
    (β := (3 / 100 : ℝ)) (z := (3 / 8 : ℝ))
    (by norm_num)
    (by norm_num [mediumCorrectionPolynomial])
    (by norm_num [mediumLogLowerThree, mediumCorrectionPolynomial,
      mediumExpNegUpper, KernelBounds.expNegTaylor9,
      KernelBounds.expNegError10, Nat.factorial])
  have hblue :
      tangentBlue (3 / 100) (3 / 8) ≤ (294 / 1000 : ℝ) := by
    apply le_trans (b := mediumBlueUpper (3 / 100) (3 / 8))
    · exact hblueApprox
    · norm_num [mediumBlueUpper, mediumLogLowerThree,
        mediumCorrectionPolynomial, mediumExpNegUpper,
        KernelBounds.expNegTaylor9, KernelBounds.expNegError10,
        Nat.factorial]
  have hmu :
      optimizationM (3 / 8) ≤ (2578 / 10000 : ℝ) := by
    apply medium_mu_upper (z := (3 / 8 : ℝ)) (by norm_num)
    norm_num [mediumExpNegUpper, KernelBounds.expNegTaylor9,
      KernelBounds.expNegError10, Nat.factorial]
  have hx := tangent_xlog_lower_of_upper_bounds
    (β := (3 / 100 : ℝ)) (z := (3 / 8 : ℝ))
    (B := (294 / 1000 : ℝ)) (M := (2578 / 10000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hblue hmu (by norm_num) (by norm_num)
  have hlogt := Real.log_le_sub_one_of_pos
    (x := (99 / 100 : ℝ)) (by norm_num)
  have hlogden := medium_log_lower_three
    (x := (199 / 100 : ℝ)) (by norm_num)
  have hexp := (medium_exp_neg_bounds
    (z := (99 / 100 : ℝ)) (by norm_num)).1
  have hP :
      0 ≤ mediumCorrectionPolynomial (33 / 1000) (99 / 100) := by
    norm_num [mediumCorrectionPolynomial]
  have hcorr :
      mediumCorrectionPolynomial (33 / 1000) (99 / 100) *
          mediumExpNegLower (99 / 100) ≤
        tangentCorrectionSlope (33 / 1000) (99 / 100) := by
    unfold tangentCorrectionSlope
    change
      mediumCorrectionPolynomial (33 / 1000) (99 / 100) *
          mediumExpNegLower (99 / 100) ≤
        mediumCorrectionPolynomial (33 / 1000) (99 / 100) *
          Real.exp (-(99 / 100))
    exact mul_le_mul_of_nonneg_left hexp hP
  have hend :
      tangentBLog (33 / 1000) (99 / 100) ≤
        tangentXLog (3 / 100) (3 / 8) := by
    unfold tangentBLog
    norm_num [mediumLogLowerBelow, mediumLogLowerThree,
      mediumExpNegLower, mediumCorrectionPolynomial,
      KernelBounds.expNegTaylor9, KernelBounds.expNegError10,
      Nat.factorial] at hx hlogt hlogden hcorr ⊢
    linarith
  intro z hz
  have hanti := tangent_xlog_antitone_medium
    (β := (3 / 100 : ℝ)) (by norm_num)
  have hzwide : z ∈ Set.Icc (0 : ℝ) (2 / 5) := by
    constructor <;> nlinarith [hz.1, hz.2]
  have hcut : (3 / 8 : ℝ) ∈ Set.Icc (0 : ℝ) (2 / 5) := by
    norm_num
  exact hend.trans (hanti hzwide hcut hz.2)

/-- The lower coordinate comparison on the second-round plateau. -/
lemma tangent_plateau_low_round2 :
    ∀ z ∈ Set.Icc (67 / 250 : ℝ) (189 / 500),
      tangentBLog (9 / 200) (99 / 100) ≤
        tangentXLog (33 / 1000) z := by
  have hblueApprox := medium_blue_upper
    (β := (33 / 1000 : ℝ)) (z := (189 / 500 : ℝ))
    (by norm_num)
    (by norm_num [mediumCorrectionPolynomial])
    (by norm_num [mediumLogLowerThree, mediumCorrectionPolynomial,
      mediumExpNegUpper, KernelBounds.expNegTaylor9,
      KernelBounds.expNegError10, Nat.factorial])
  have hblue :
      tangentBlue (33 / 1000) (189 / 500) ≤ (295 / 1000 : ℝ) := by
    apply le_trans (b := mediumBlueUpper (33 / 1000) (189 / 500))
    · exact hblueApprox
    · norm_num [mediumBlueUpper, mediumLogLowerThree,
        mediumCorrectionPolynomial, mediumExpNegUpper,
        KernelBounds.expNegTaylor9, KernelBounds.expNegError10,
        Nat.factorial]
  have hmu :
      optimizationM (189 / 500) ≤ (2591 / 10000 : ℝ) := by
    apply medium_mu_upper (z := (189 / 500 : ℝ)) (by norm_num)
    norm_num [mediumExpNegUpper, KernelBounds.expNegTaylor9,
      KernelBounds.expNegError10, Nat.factorial]
  have hx := tangent_xlog_lower_of_upper_bounds
    (β := (33 / 1000 : ℝ)) (z := (189 / 500 : ℝ))
    (B := (295 / 1000 : ℝ)) (M := (2591 / 10000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hblue hmu (by norm_num) (by norm_num)
  have hlogt := Real.log_le_sub_one_of_pos
    (x := (99 / 100 : ℝ)) (by norm_num)
  have hlogden := medium_log_lower_three
    (x := (199 / 100 : ℝ)) (by norm_num)
  have hexp := (medium_exp_neg_bounds
    (z := (99 / 100 : ℝ)) (by norm_num)).1
  have hP :
      0 ≤ mediumCorrectionPolynomial (9 / 200) (99 / 100) := by
    norm_num [mediumCorrectionPolynomial]
  have hcorr :
      mediumCorrectionPolynomial (9 / 200) (99 / 100) *
          mediumExpNegLower (99 / 100) ≤
        tangentCorrectionSlope (9 / 200) (99 / 100) := by
    unfold tangentCorrectionSlope
    change
      mediumCorrectionPolynomial (9 / 200) (99 / 100) *
          mediumExpNegLower (99 / 100) ≤
        mediumCorrectionPolynomial (9 / 200) (99 / 100) *
          Real.exp (-(99 / 100))
    exact mul_le_mul_of_nonneg_left hexp hP
  have hend :
      tangentBLog (9 / 200) (99 / 100) ≤
        tangentXLog (33 / 1000) (189 / 500) := by
    unfold tangentBLog
    norm_num [mediumLogLowerBelow, mediumLogLowerThree,
      mediumExpNegLower, mediumCorrectionPolynomial,
      KernelBounds.expNegTaylor9, KernelBounds.expNegError10,
      Nat.factorial] at hx hlogt hlogden hcorr ⊢
    linarith
  intro z hz
  have hanti := tangent_xlog_antitone_medium
    (β := (33 / 1000 : ℝ)) (by norm_num)
  have hzwide : z ∈ Set.Icc (0 : ℝ) (2 / 5) := by
    constructor <;> nlinarith [hz.1, hz.2]
  have hcut : (189 / 500 : ℝ) ∈ Set.Icc (0 : ℝ) (2 / 5) := by
    norm_num
  exact hend.trans (hanti hzwide hcut hz.2)

/-- The lower coordinate comparison on the first-round plateau. -/
lemma tangent_plateau_low_round1 :
    ∀ z ∈ Set.Icc (269 / 1000 : ℝ) (387 / 1000),
      tangentBLog (2 / 25) (99 / 100) ≤
        tangentXLog (9 / 200) z := by
  have hblueApprox := medium_blue_upper
    (β := (9 / 200 : ℝ)) (z := (387 / 1000 : ℝ))
    (by norm_num)
    (by norm_num [mediumCorrectionPolynomial])
    (by norm_num [mediumLogLowerThree, mediumCorrectionPolynomial,
      mediumExpNegUpper, KernelBounds.expNegTaylor9,
      KernelBounds.expNegError10, Nat.factorial])
  have hblue :
      tangentBlue (9 / 200) (387 / 1000) ≤ (2975 / 10000 : ℝ) := by
    apply le_trans (b := mediumBlueUpper (9 / 200) (387 / 1000))
    · exact hblueApprox
    · norm_num [mediumBlueUpper, mediumLogLowerThree,
        mediumCorrectionPolynomial, mediumExpNegUpper,
        KernelBounds.expNegTaylor9, KernelBounds.expNegError10,
        Nat.factorial]
  have hmu :
      optimizationM (387 / 1000) ≤ (2629 / 10000 : ℝ) := by
    apply medium_mu_upper (z := (387 / 1000 : ℝ)) (by norm_num)
    norm_num [mediumExpNegUpper, KernelBounds.expNegTaylor9,
      KernelBounds.expNegError10, Nat.factorial]
  have hx := tangent_xlog_lower_of_upper_bounds
    (β := (9 / 200 : ℝ)) (z := (387 / 1000 : ℝ))
    (B := (2975 / 10000 : ℝ)) (M := (2629 / 10000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hblue hmu (by norm_num) (by norm_num)
  have hlogt := Real.log_le_sub_one_of_pos
    (x := (99 / 100 : ℝ)) (by norm_num)
  have hlogden := medium_log_lower_three
    (x := (199 / 100 : ℝ)) (by norm_num)
  have hexp := (medium_exp_neg_bounds
    (z := (99 / 100 : ℝ)) (by norm_num)).1
  have hP :
      0 ≤ mediumCorrectionPolynomial (2 / 25) (99 / 100) := by
    norm_num [mediumCorrectionPolynomial]
  have hcorr :
      mediumCorrectionPolynomial (2 / 25) (99 / 100) *
          mediumExpNegLower (99 / 100) ≤
        tangentCorrectionSlope (2 / 25) (99 / 100) := by
    unfold tangentCorrectionSlope
    change
      mediumCorrectionPolynomial (2 / 25) (99 / 100) *
          mediumExpNegLower (99 / 100) ≤
        mediumCorrectionPolynomial (2 / 25) (99 / 100) *
          Real.exp (-(99 / 100))
    exact mul_le_mul_of_nonneg_left hexp hP
  have hend :
      tangentBLog (2 / 25) (99 / 100) ≤
        tangentXLog (9 / 200) (387 / 1000) := by
    unfold tangentBLog
    norm_num [mediumLogLowerBelow, mediumLogLowerThree,
      mediumExpNegLower, mediumCorrectionPolynomial,
      KernelBounds.expNegTaylor9, KernelBounds.expNegError10,
      Nat.factorial] at hx hlogt hlogden hcorr ⊢
    linarith
  intro z hz
  have hanti := tangent_xlog_antitone_medium
    (β := (9 / 200 : ℝ)) (by norm_num)
  have hzwide : z ∈ Set.Icc (0 : ℝ) (2 / 5) := by
    constructor <;> nlinarith [hz.1, hz.2]
  have hcut : (387 / 1000 : ℝ) ∈ Set.Icc (0 : ℝ) (2 / 5) := by
    norm_num
  exact hend.trans (hanti hzwide hcut hz.2)

def plateauExpNegUpper (z : ℝ) : ℝ :=
  1 - z + z ^ 2 / 2 - z ^ 3 / 6 + z ^ 4 / 24

lemma exp_neg_upper_plateau {z : ℝ}
    (hz : z ∈ Set.Icc (0 : ℝ) (2 / 5)) :
    Real.exp (-z) ≤ plateauExpNegUpper z := by
  have hz' : z ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hz.1, hz.2]
  have hupper := (medium_exp_neg_bounds hz').2
  have h₁ :
      0 ≤ z ^ 5 * (1 / 120 - z / 720) := by
    exact mul_nonneg (pow_nonneg hz.1 5) (by nlinarith [hz.2])
  have h₂ :
      0 ≤ z ^ 7 * (1 / 5040 - z / 40320) := by
    exact mul_nonneg (pow_nonneg hz.1 7) (by nlinarith [hz.2])
  have h₃ :
      0 ≤ z ^ 9 * (1 / 362880 - 11 * z / 36288000) := by
    exact mul_nonneg (pow_nonneg hz.1 9) (by nlinarith [hz.2])
  dsimp [mediumExpNegUpper, KernelBounds.expNegTaylor9,
    KernelBounds.expNegError10, plateauExpNegUpper] at hupper ⊢
  norm_num [Nat.factorial] at hupper ⊢
  nlinarith [h₁, h₂, h₃]

def plateauInvOneAddUpper (z : ℝ) : ℝ :=
  1 - z + z ^ 2 - z ^ 3 + z ^ 4 - z ^ 5 + z ^ 6

private lemma inv_one_add_upper_plateau {z : ℝ}
    (hz : z ∈ Set.Icc (0 : ℝ) (2 / 5)) :
    (1 + z)⁻¹ ≤ plateauInvOneAddUpper z := by
  have hplus : 0 < 1 + z := by linarith [hz.1]
  rw [inv_le_iff_one_le_mul₀ hplus]
  unfold plateauInvOneAddUpper
  nlinarith [pow_nonneg hz.1 7]

private def plateauExpPosUpper (q : ℝ) : ℝ :=
  1 + q + q ^ 2 / 2 + q ^ 3 / 6 + q ^ 4 / 24 + q ^ 5 / 100

private lemma exp_pos_upper_plateau {q : ℝ}
    (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    Real.exp q ≤ plateauExpPosUpper q := by
  have h := Real.exp_bound' hq.1 hq.2 (n := 5) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial,
    plateauExpPosUpper] at h ⊢
  linarith

def plateauExpPosCoarse (q : ℝ) : ℝ :=
  1 + q + q ^ 2

private lemma exp_pos_coarse_plateau {q : ℝ}
    (hq : q ∈ Set.Icc (0 : ℝ) (1 / 5)) :
    Real.exp q ≤ plateauExpPosCoarse q := by
  have hq' : q ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hupper := exp_pos_upper_plateau hq'
  have hq2 : q ^ 2 ≤ (1 / 5 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg hq.1 (sub_nonneg.mpr hq.2)]
  have hq3 : q ^ 3 ≤ (1 / 5 : ℝ) ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg q) hq.1,
      mul_nonneg (sq_nonneg q) (sub_nonneg.mpr hq.2)]
  have hcoef :
      0 ≤ 1 / 2 - q / 6 - q ^ 2 / 24 - q ^ 3 / 100 := by
    nlinarith [hq.2, hq2, hq3]
  have hrest :=
    mul_nonneg (sq_nonneg q) hcoef
  dsimp [plateauExpPosUpper] at hupper
  dsimp [plateauExpPosCoarse]
  nlinarith [hrest]

def plateauBlueRawUpper (β z : ℝ) : ℝ :=
  let q :=
    -mediumCorrectionPolynomial β z * plateauExpNegUpper z
  z * plateauInvOneAddUpper z * plateauExpPosCoarse q

lemma tangent_blue_le_plateau_raw {β z : ℝ}
    (hz : z ∈ Set.Icc (0 : ℝ) (2 / 5))
    (hP : mediumCorrectionPolynomial β z ≤ 0)
    (hq : -mediumCorrectionPolynomial β z *
        plateauExpNegUpper z ∈ Set.Icc (0 : ℝ) (1 / 5)) :
    tangentBlue β z ≤ plateauBlueRawUpper β z := by
  let q : ℝ :=
    -mediumCorrectionPolynomial β z * plateauExpNegUpper z
  have hez := exp_neg_upper_plateau hz
  have hnegP : 0 ≤ -mediumCorrectionPolynomial β z := by
    linarith
  have hslope :
      -tangentCorrectionSlope β z ≤ q := by
    rw [show
      tangentCorrectionSlope β z =
        mediumCorrectionPolynomial β z * Real.exp (-z) by rfl]
    calc
      -(mediumCorrectionPolynomial β z * Real.exp (-z)) =
          -mediumCorrectionPolynomial β z * Real.exp (-z) := by ring
      _ ≤ q := by
        dsimp [q]
        exact mul_le_mul_of_nonneg_left hez hnegP
  have hexp :
      Real.exp (-tangentCorrectionSlope β z) ≤
        plateauExpPosCoarse q :=
    (Real.exp_le_exp.mpr hslope).trans (exp_pos_coarse_plateau hq)
  have hinv := inv_one_add_upper_plateau hz
  have hinv0 : 0 ≤ (1 + z)⁻¹ :=
    inv_nonneg.mpr (by linarith [hz.1])
  have hpoly0 : 0 ≤ plateauInvOneAddUpper z :=
    hinv0.trans hinv
  have hexp0 : 0 ≤ Real.exp (-tangentCorrectionSlope β z) :=
    Real.exp_pos _ |>.le
  have hproduct :
      (1 + z)⁻¹ * Real.exp (-tangentCorrectionSlope β z) ≤
        plateauInvOneAddUpper z * plateauExpPosCoarse q :=
    mul_le_mul hinv hexp hexp0 hpoly0
  have hplus : 0 < 1 + z := by linarith [hz.1]
  unfold tangentBlue plateauBlueRawUpper
  dsimp only
  rw [show
      -Real.log (1 + z) - tangentCorrectionSlope β z =
        -Real.log (1 + z) + -tangentCorrectionSlope β z by ring,
    Real.exp_add, Real.exp_neg, Real.exp_log hplus]
  calc
    z * ((1 + z)⁻¹ * Real.exp (-tangentCorrectionSlope β z)) ≤
        z * (plateauInvOneAddUpper z * plateauExpPosCoarse q) :=
      mul_le_mul_of_nonneg_left hproduct hz.1
    _ = z * plateauInvOneAddUpper z *
        plateauExpPosCoarse
          (-mediumCorrectionPolynomial β z * plateauExpNegUpper z) := by
      dsimp [q]
      ring

def plateauMuUpper (z : ℝ) : ℝ :=
  z * plateauExpNegUpper z

private lemma optimizationM_le_plateau_mu {z : ℝ}
    (hz : z ∈ Set.Icc (0 : ℝ) (2 / 5)) :
    optimizationM z ≤ plateauMuUpper z := by
  unfold optimizationM plateauMuUpper
  exact mul_le_mul_of_nonneg_left (exp_neg_upper_plateau hz) hz.1

def plateauBlueUpperRound3 (z : ℝ) : ℝ :=
  -(2865515847 / 10000000000) * z ^ 4 +
    12872073941 / 10000000000 * z ^ 3 -
    4196550333 / 2500000000 * z ^ 2 +
    6185391153 / 5000000000 * z +
    24086447 / 5000000000

private lemma plateau_blue_raw_le_round3 {z : ℝ}
    (hz : z ∈ Set.Icc (67 / 250 : ℝ) (3 / 8)) :
    plateauBlueRawUpper (3 / 100) z ≤
      plateauBlueUpperRound3 z := by
  let u : ℝ := (1000 * z - 268) / 107
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have h := KernelBounds.bernstein_sum_nonneg 21
    [195943195284545904969364990890045313445280748713432471916511232,
      3879701699243022485256192555957853674451894690096627970998272000,
      38079981415194540302203834379380742907797637516590695055360000000,
      242678751092498637040133163051574853359970687914443014144000000000,
      1111400846204560783940323899717061800262132706124496896000000000000,
      3851800591897983448943687360742508106561756861005824000000000000000,
      10424322901576656746522240905580181061509639877632000000000000000000,
      22505415250537905509897340468309109155386189728000000000000000000000,
      39363705154239948471875115238276320986200282500000000000000000000000,
      56426987047857179608733922628498477903052828125000000000000000000000,
      66863162653503412267894382580125959774868652343750000000000000000000,
      65888708646021778031773685238402941056198120117187500000000000000000,
      54179983989628077913172958874513856814384460449218750000000000000000,
      37187400040015305051350401260574286788702011108398437500000000000000,
      21223890510557875594472984578812443651258945465087890625000000000000,
      9978032188560024285592291037072689505293965339660644531250000000000,
      3798922999969185611292891521754003406385891139507293701171875000000,
      1139363006261190303252618884130869901127880439162254333496093750000,
      257722559383035865803707552140352277092461008578538894653320312500,
      40967359282263480671141906837906532246051938273012638092041015625,
      4025045817270789820100278300074592152668628841638565063476562500,
      180002265131751261396347851828636521531734615564346313476562500] hu
  have hid :
      plateauBlueUpperRound3 z -
          plateauBlueRawUpper (3 / 100) z =
        (∑ i ∈ Finset.range 22,
          ((List.getD [195943195284545904969364990890045313445280748713432471916511232,
              3879701699243022485256192555957853674451894690096627970998272000,
              38079981415194540302203834379380742907797637516590695055360000000,
              242678751092498637040133163051574853359970687914443014144000000000,
              1111400846204560783940323899717061800262132706124496896000000000000,
              3851800591897983448943687360742508106561756861005824000000000000000,
              10424322901576656746522240905580181061509639877632000000000000000000,
              22505415250537905509897340468309109155386189728000000000000000000000,
              39363705154239948471875115238276320986200282500000000000000000000000,
              56426987047857179608733922628498477903052828125000000000000000000000,
              66863162653503412267894382580125959774868652343750000000000000000000,
              65888708646021778031773685238402941056198120117187500000000000000000,
              54179983989628077913172958874513856814384460449218750000000000000000,
              37187400040015305051350401260574286788702011108398437500000000000000,
              21223890510557875594472984578812443651258945465087890625000000000000,
              9978032188560024285592291037072689505293965339660644531250000000000,
              3798922999969185611292891521754003406385891139507293701171875000000,
              1139363006261190303252618884130869901127880439162254333496093750000,
              257722559383035865803707552140352277092461008578538894653320312500,
              40967359282263480671141906837906532246051938273012638092041015625,
              4025045817270789820100278300074592152668628841638565063476562500,
              180002265131751261396347851828636521531734615564346313476562500]
            i 0 : ℕ) : ℝ) *
            u ^ i * (1 - u) ^ (21 - i)) /
          90000000000000000000000000000000000000000000000000000000000000000000 := by
    dsimp [u, plateauBlueUpperRound3, plateauBlueRawUpper,
      plateauInvOneAddUpper, plateauExpPosCoarse,
      mediumCorrectionPolynomial, plateauExpNegUpper]
    norm_num [Finset.sum_range_succ]
    ring
  rw [← sub_nonneg, hid]
  exact div_nonneg h (by norm_num)

private lemma tangent_blue_le_round3 {z : ℝ}
    (hz : z ∈ Set.Icc (67 / 250 : ℝ) (3 / 8)) :
    tangentBlue (3 / 100) z ≤ plateauBlueUpperRound3 z := by
  have hzwide : z ∈ Set.Icc (0 : ℝ) (2 / 5) := by
    constructor <;> nlinarith [hz.1, hz.2]
  have hP :
      mediumCorrectionPolynomial (3 / 100) z ≤ 0 := by
    dsimp [mediumCorrectionPolynomial]
    nlinarith [hzwide.1, hzwide.2, sq_nonneg z,
      mul_nonneg (sq_nonneg z) hzwide.1]
  have hq :
      -mediumCorrectionPolynomial (3 / 100) z *
          plateauExpNegUpper z ∈ Set.Icc (0 : ℝ) (1 / 5) := by
    have hnegP0 :
        0 ≤ -mediumCorrectionPolynomial (3 / 100) z := by
      linarith
    have hnegP1 :
        -mediumCorrectionPolynomial (3 / 100) z ≤ 1 / 5 := by
      have hz3 : z ^ 3 ≤ (2 / 5 : ℝ) ^ 3 := by
        nlinarith [hzwide.1, hzwide.2, sq_nonneg z,
          mul_nonneg (sq_nonneg z) hzwide.1,
          mul_nonneg (sq_nonneg z) (sub_nonneg.mpr hzwide.2)]
      dsimp [mediumCorrectionPolynomial]
      nlinarith [hz.1, hz3, sq_nonneg z]
    have he0 : 0 ≤ plateauExpNegUpper z :=
      (Real.exp_pos (-z)).le.trans (exp_neg_upper_plateau hzwide)
    have he1 : plateauExpNegUpper z ≤ 1 := by
      have hcoef :
          0 ≤ 1 - z / 2 + z ^ 2 / 6 - z ^ 3 / 24 := by
        nlinarith [hzwide.1, hzwide.2, sq_nonneg z,
          mul_nonneg (sq_nonneg z) hzwide.1]
      dsimp [plateauExpNegUpper]
      nlinarith [mul_nonneg hzwide.1 hcoef]
    constructor
    · exact mul_nonneg hnegP0 he0
    · calc
        -mediumCorrectionPolynomial (3 / 100) z *
            plateauExpNegUpper z ≤ (1 / 5 : ℝ) * 1 :=
          mul_le_mul hnegP1 he1 he0 (by norm_num)
        _ = 1 / 5 := by ring
  exact (tangent_blue_le_plateau_raw hzwide hP hq).trans
    (plateau_blue_raw_le_round3 hz)

def plateauSumLower (β : ℝ) : ℝ :=
  let t : ℝ := 99 / 100
  let aCoefficient :=
    t ^ 2 *
      (1 / 4 + β + (4 / 25 - β) * t - 2 / 25 * t ^ 2)
  (-mediumLogUpperSix (1 + t) +
      aCoefficient * mediumExpNegLower t +
    mediumLogLowerBelow t - mediumLogUpperSix (1 + t) -
      mediumCorrectionPolynomial β t * mediumExpNegUpper t)

private lemma plateau_sum_lower_le {β : ℝ}
    (hβ : β ∈ Set.Icc 0 (2 / 25)) :
    plateauSumLower β ≤
      tangentALog β (99 / 100) + tangentBLog β (99 / 100) := by
  let t : ℝ := 99 / 100
  let aCoefficient : ℝ :=
    t ^ 2 *
      (1 / 4 + β + (4 / 25 - β) * t - 2 / 25 * t ^ 2)
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [t]
    norm_num
  have hlogUpper := medium_log_upper_six
    (x := 1 + t) (by dsimp [t]; norm_num)
  have hlogLower := medium_log_lower_below
    (x := t) (by dsimp [t]; norm_num) (by dsimp [t]; norm_num)
  have hexp := medium_exp_neg_bounds ht
  have hcoef : 0 ≤ aCoefficient := by
    dsimp [aCoefficient, t]
    nlinarith [hβ.1, hβ.2]
  have hAexp :
      aCoefficient * mediumExpNegLower t ≤
        aCoefficient * Real.exp (-t) :=
    mul_le_mul_of_nonneg_left hexp.1 hcoef
  have hP :
      0 ≤ mediumCorrectionPolynomial β t := by
    dsimp [mediumCorrectionPolynomial, t]
    nlinarith [hβ.1, hβ.2]
  have hBexp :
      mediumCorrectionPolynomial β t * Real.exp (-t) ≤
        mediumCorrectionPolynomial β t * mediumExpNegUpper t :=
    mul_le_mul_of_nonneg_left hexp.2 hP
  unfold tangentALog tangentBLog
  rw [show
    tangentCorrectionSlope β (99 / 100) =
      mediumCorrectionPolynomial β (99 / 100) *
        Real.exp (-(99 / 100)) by rfl]
  dsimp [plateauSumLower, aCoefficient, t] at hlogUpper hlogLower hAexp hBexp ⊢
  nlinarith

def plateauLogThreeClosed (x : ℝ) : ℝ :=
  2 * (x - 1) *
    (23 * x ^ 4 + 48 * x ^ 3 + 98 * x ^ 2 + 48 * x + 23) /
      (15 * (x + 1) ^ 5)

lemma medium_log_lower_three_closed {x : ℝ}
    (hx : x + 1 ≠ 0) :
    mediumLogLowerThree x = plateauLogThreeClosed x := by
  dsimp [mediumLogLowerThree, plateauLogThreeClosed]
  field_simp [hx]
  ring

lemma medium_log_upper_below_closed {x : ℝ}
    (hx0 : x ≠ 0) (hx1 : x + 1 ≠ 0) :
    mediumLogUpperBelow x = plateauLogThreeClosed x := by
  have hpoly :
      1 + x * 5 + x ^ 2 * 10 + x ^ 3 * 10 +
          x ^ 4 * 5 + x ^ 5 ≠ 0 := by
    rw [show
      1 + x * 5 + x ^ 2 * 10 + x ^ 3 * 10 +
          x ^ 4 * 5 + x ^ 5 = (x + 1) ^ 5 by ring]
    exact pow_ne_zero 5 hx1
  dsimp [mediumLogUpperBelow, mediumLogLowerThree,
    plateauLogThreeClosed]
  field_simp [hx0, hx1]
  ring_nf
  field_simp [hpoly]
  ring

def plateauLogLowerBelowOneSub (x : ℝ) : ℝ :=
  -x * (3 * x ^ 4 - 16 * x ^ 3 + 64 * x ^ 2 - 96 * x + 48) /
    (6 * (2 - x) ^ 3 * (1 - x))

lemma medium_log_lower_below_one_sub {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x < 1) :
    mediumLogLowerBelow (1 - x) =
      plateauLogLowerBelowOneSub x := by
  have htwo : 0 < 2 - x := by linarith
  have hone : 0 < 1 - x := by linarith
  have hy0 : 0 ≤ x / (2 - x) :=
    div_nonneg hx0 htwo.le
  have hy1 : x / (2 - x) < 1 := by
    rw [div_lt_one htwo]
    linarith
  have hysquare : 0 < 1 - (x / (2 - x)) ^ 2 := by
    nlinarith [mul_nonneg hy0 (sub_nonneg.mpr hy1.le)]
  dsimp [mediumLogLowerBelow, plateauLogLowerBelowOneSub]
  field_simp [htwo.ne', hone.ne', hysquare.ne']
  ring_nf
  field_simp [hone.ne']
  ring

def plateauXLogLower (B z : ℝ) : ℝ :=
  let M := plateauMuUpper z
  mediumLogLowerBelow (1 - B) * (1 - M)⁻¹ +
    mediumLogLowerBelow (1 - M)

def plateauBookLower (β₀ β₁ : ℝ)
    (B : ℝ → ℝ) (z : ℝ) : ℝ :=
  (1 + z) * mediumLogLowerThree (1 + z) +
    (-(1 / 4) * z + β₁ * z ^ 2 + 2 / 25 * z ^ 3) *
      plateauExpNegUpper z +
    ((1 - z) * plateauXLogLower (B z) z - z ^ 2 +
      z * plateauSumLower β₀ -
      z * mediumLogUpperBelow z) / 2

lemma bernstein_sum_pos_of_ends
    (n : ℕ) (coeffs : List ℕ) {z : ℝ}
    (hz : z ∈ Set.Icc 0 1)
    (hfirst : 0 < coeffs.getD 0 0)
    (hlast : 0 < coeffs.getD n 0) :
    0 < ∑ i ∈ Finset.range (n + 1),
      (coeffs.getD i 0 : ℝ) * z ^ i * (1 - z) ^ (n - i) := by
  have hterm (i : ℕ) :
      0 ≤ (coeffs.getD i 0 : ℝ) * z ^ i *
        (1 - z) ^ (n - i) :=
    mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hz.1 _))
      (pow_nonneg (sub_nonneg.mpr hz.2) _)
  by_cases hhalf : z ≤ 1 / 2
  · have hone : 0 < 1 - z := by linarith
    have hzero :
        0 < (coeffs.getD 0 0 : ℝ) * z ^ 0 *
          (1 - z) ^ (n - 0) := by
      norm_num
      exact mul_pos (Nat.cast_pos.mpr hfirst) (pow_pos hone n)
    exact hzero.trans_le (Finset.single_le_sum
      (fun i _ => hterm i) (by simp))
  · have hzpos : 0 < z := by linarith
    have hn :
        0 < (coeffs.getD n 0 : ℝ) * z ^ n *
          (1 - z) ^ (n - n) := by
      norm_num
      exact mul_pos (Nat.cast_pos.mpr hlast) (pow_pos hzpos n)
    exact hn.trans_le (Finset.single_le_sum
      (fun i _ => hterm i) (by simp))

lemma plateau_book_lower_le
    {β₀ β₁ z B : ℝ}
    (hβ₀ : β₀ ∈ Set.Icc 0 (2 / 25))
    (hβ₁ : β₁ ∈ Set.Icc 0 (2 / 25))
    (hz : z ∈ Set.Icc (0 : ℝ) (2 / 5))
    (hz0 : 0 < z)
    (hB0 : 0 ≤ B) (hB1 : B < 1)
    (hB : tangentBlue β₁ z ≤ B)
    (hM0 : 0 ≤ plateauMuUpper z)
    (hM1 : plateauMuUpper z < 1) :
    plateauBookLower β₀ β₁ (fun _ => B) z ≤
      tangentCleanBookMargin β₁ z
        (tangentALog β₀ (99 / 100) +
          tangentBLog β₀ (99 / 100) -
          tangentXLog β₁ z - Real.log z) := by
  have hz1 : z ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hz.1, hz.2]
  have hM := optimizationM_le_plateau_mu hz
  have hX := tangent_xlog_lower_of_upper_bounds
    hβ₁.1 hz1 hB0 hM0 hB hM hB1 hM1
  change plateauXLogLower B z ≤ tangentXLog β₁ z at hX
  have hentropy := medium_log_lower_three
    (show (1 : ℝ) ≤ 1 + z by linarith [hz.1])
  have hP :
      -(1 / 4) * z + β₁ * z ^ 2 + 2 / 25 * z ^ 3 ≤ 0 := by
    have hz2 : z ^ 2 ≤ (2 / 5 : ℝ) * z := by
      nlinarith [mul_nonneg hz.1 (sub_nonneg.mpr hz.2)]
    have hz3 : z ^ 3 ≤ (2 / 5 : ℝ) ^ 2 * z := by
      nlinarith [mul_nonneg (sq_nonneg z) hz.1,
        mul_nonneg (sq_nonneg z) (sub_nonneg.mpr hz.2)]
    nlinarith [hβ₁.2, hz.1, hz2, hz3]
  have hcorrection :
      (-(1 / 4) * z + β₁ * z ^ 2 + 2 / 25 * z ^ 3) *
          plateauExpNegUpper z ≤
        ramseyCorrection β₁ z := by
    unfold ramseyCorrection
    exact mul_le_mul_of_nonpos_left (exp_neg_upper_plateau hz) hP
  have hsum := plateau_sum_lower_le hβ₀
  have hlog := medium_log_upper_below
    (x := z) hz0 (by nlinarith [hz.2])
  have hxterm :
      (1 - z) * plateauXLogLower B z ≤
        (1 - z) * tangentXLog β₁ z :=
    mul_le_mul_of_nonneg_left hX (by nlinarith [hz.2])
  have hsumterm :
      z * plateauSumLower β₀ ≤
        z * (tangentALog β₀ (99 / 100) +
          tangentBLog β₀ (99 / 100)) :=
    mul_le_mul_of_nonneg_left hsum hz.1
  have hlogterm :
      -z * mediumLogUpperBelow z ≤ -z * Real.log z :=
    mul_le_mul_of_nonpos_left hlog (by linarith [hz.1])
  unfold tangentCleanBookMargin
  dsimp [plateauBookLower]
  nlinarith [mul_le_mul_of_nonneg_left hentropy
    (show (0 : ℝ) ≤ 1 + z by linarith [hz.1])]

private def decimalNat : List ℕ → ℕ
  | [] => 0
  | chunk :: chunks =>
      chunk * (10 ^ 18) ^ chunks.length +
        decimalNat chunks

private def plateauBookPowerCoeffsRound3 : List ℤ :=
  [
    -(decimalNat
      [9674136052, 418653406653909445, 82512061520140153,
        341287425994341891, 558600778104631604, 303560389427200000,
        0] : ℤ),
    (decimalNat
      [1960345002431, 705719801519951937, 858099359708508068,
        437327295433700014, 841581562682178951, 411098107971616806,
        982986364685910016] : ℤ),
    -(decimalNat
      [14349785771613, 160509787560755033, 690125023692374932,
        33337815986605093, 178733490984150772, 768063063860279529,
        849504426606198784] : ℤ),
    (decimalNat
      [45229880253525, 320104364686904946, 609457860212630614,
        820258030749064873, 634821097541275227, 820367805768642712,
        98947781634293760] : ℤ),
    -(decimalNat
      [105147127859190, 216265033869492475, 767960088655488610,
        721923753098969077, 815580073406450381, 456220283959938754,
        575411510910124032] : ℤ),
    (decimalNat
      [223854130316804, 320227613407764462, 33017965202414136,
        505081557925717978, 375213848181719064, 531873736109353835,
        301703399545765888] : ℤ),
    -(decimalNat
      [382340361571812, 935103424588945390, 352549238320211845,
        775011761737642201, 517561518494442756, 567215844375884039,
        142392118751789056] : ℤ),
    (decimalNat
      [601881330234124, 169111535982471525, 678646121302939847,
        269244182585421169, 641641390237739675, 539136839698083515,
        364259042808561664] : ℤ),
    -(decimalNat
      [833004026760657, 127239528294717330, 154806912046193906,
        23535508898280408, 81539597943763953, 93435794466107593,
        39643582429396992] : ℤ),
    (decimalNat
      [1022511657479170, 362991116167882598, 834702106830050778,
        415969276368934273, 569432363545940032, 89429629122407372,
        57822038667493376] : ℤ),
    -(decimalNat
      [1124394432248816, 756535712824475244, 434363830960338507,
        864794538098177937, 830029388253779381, 637872493441151791,
        737036831052857344] : ℤ),
    (decimalNat
      [1090936538600607, 295442272006610560, 594769769695314720,
        809501713123752548, 462201392756789435, 47497763837326246,
        850727331202990080] : ℤ),
    -(decimalNat
      [928208895151364, 463080453928127082, 697165410944348862,
        362451330143238660, 73272400124331302, 265670006244192966,
        396208712618295296] : ℤ),
    (decimalNat
      [681422899068829, 906048211163479130, 727029791408383204,
        535746328870767578, 169312968995102414, 288598042545721612,
        840670737969979392] : ℤ),
    -(decimalNat
      [407005921026143, 457105217436319224, 459702328988416310,
        979046744212425757, 46867743072509135, 349524420426429393,
        551576423364141056] : ℤ),
    (decimalNat
      [167578951376768, 940092094407884013, 587404059366029050,
        893879659979486956, 534848278396614314, 397951598233753977,
        464594986401337344] : ℤ),
    -(decimalNat
      [3197571978911, 636515453078627130, 694351035468339038,
        580154573391733675, 144485324322619532, 332931269700983725,
        416834085729218560] : ℤ),
    -(decimalNat
      [79367176237015, 930163278202522921, 605471967016484158,
        266853602509907926, 603675236586731266, 122666944368755597,
        273318543317365760] : ℤ),
    (decimalNat
      [95833182282773, 715905965946920782, 410698085708525614,
        633011599498040316, 826214609040020438, 429403466252825458,
        488394134507113472] : ℤ),
    -(decimalNat
      [74753169988186, 154020620164401474, 823814620949837937,
        858533820158164823, 816773341511573699, 13408642713079878,
        542871238950155776] : ℤ),
    (decimalNat
      [42935446226814, 568721852342683270, 542275200659109851,
        634601591065888336, 904129915160267890, 726235915883757996,
        856380768029422848] : ℤ),
    -(decimalNat
      [16527395755926, 331657505863790070, 292318375866307105,
        545433935987252035, 974172815992975728, 6051670576938033,
        535958473462030464] : ℤ),
    (decimalNat
      [1182958132017, 420782497394758190, 490180272090373550,
        383234326640314821, 355579520224512221, 727898584211111955,
        681783498792822656] : ℤ),
    (decimalNat
      [4591161071443, 811998787181019726, 427551625884099128,
        364061184440274551, 434427091688026122, 156655674802512265,
        378578410195435520] : ℤ),
    -(decimalNat
      [4837939871472, 851961380455246435, 690429211922770686,
        968767121495702172, 998662522877557454, 827367792752690729,
        298346035679722368] : ℤ),
    (decimalNat
      [3085235253271, 544461413517123343, 4299768070939092,
        429424183632363563, 638241658905537623, 206000465857218699,
        69087234113197280] : ℤ),
    -(decimalNat
      [1342302340216, 548509555200806635, 565684098390536704,
        89850689833732412, 593948719815129750, 811411184568091635,
        303961800007563184] : ℤ),
    (decimalNat
      [284423561916, 741821419605504695, 191059411797063332,
        905463187373658049, 446477751661279530, 530007738081300736,
        181891582377448752] : ℤ),
    (decimalNat
      [133564180700, 172487605051140941, 539712137939009669,
        603366436008985322, 404447675691321428, 556413057564010879,
        497360550982853056] : ℤ),
    -(decimalNat
      [186045361568, 34749368883765382, 192380249669386529,
        957864496306301781, 353694355442300715, 164011216694097030,
        374952701437959520] : ℤ),
    (decimalNat
      [113184500629, 418049182779388801, 988326847842816873,
        621954779802466120, 999597192762335857, 912238377063409427,
        221887230684880896] : ℤ),
    -(decimalNat
      [40392392491, 795785866353363988, 898115914646392920,
        39147256178600491, 314959668494362775, 803363430786645518,
        754739725628758640] : ℤ),
    (decimalNat
      [2397118255, 859640353536235029, 49668467260320682,
        380938064179537323, 87910963101439848, 336740742011422439,
        466325917592609480] : ℤ),
    (decimalNat
      [8392031439, 661427722635552563, 768843845618227166,
        108584896749471105, 378543793917463789, 146461592176700915,
        129792885029478176] : ℤ),
    -(decimalNat
      [7361266789, 845021846327683656, 166573300841204039,
        99437381463874261, 600223673419746929, 701131466034929832,
        780484948428064200] : ℤ),
    (decimalNat
      [4073220904, 912973312700252830, 950065413515374517,
        945386763533857504, 413163865554244042, 593614232434636148,
        606868331154160168] : ℤ),
    -(decimalNat
      [1796248738, 342290802861257882, 28060519042740778,
        323474245402223108, 151047453396450751, 454755918550758131,
        694247197193227776] : ℤ),
    (decimalNat
      [713697562, 244390020220669849, 222263523223574932,
        857616508171055480, 191538500208105021, 853548790567439392,
        179816592028989870] : ℤ),
    -(decimalNat
      [286328868, 53885820502421080, 187780771573771847,
        354008280106817988, 925306079464432251, 731434134883457780,
        870796491042739347] : ℤ),
    (decimalNat
      [121994839, 772867448715803456, 192415687237761032,
        332146707693311883, 264469041680109035, 817399451577818833,
        167533040249334039] : ℤ),
    -(decimalNat
      [51658631, 877401237273770702, 282057588809440560,
        630209921223951165, 387649707390848253, 17292543860261567,
        202904038526430116] : ℤ),
    (decimalNat
      [19317051, 163229467732983224, 942747733174322279,
        877023611645550864, 89177361543216293, 931161691915380651,
        545867252263504624] : ℤ),
    -(decimalNat
      [5634147, 520177750410296346, 588969114767753277,
        224107655930652126, 683954931730455223, 429340334372201187,
        663320739967143474] : ℤ),
    (decimalNat
      [994165, 92384100438271967, 627744731560320576,
        81268208243977711, 286748487504909937, 51671609689067146,
        976125837029740546] : ℤ),
    (decimalNat
      [68474, 781433864800833277, 87049369511088182,
        48652255598345253, 433407115157610414, 917962481527897850,
        415783667396393780] : ℤ),
    -(decimalNat
      [126883, 103875315923416971, 763365756776595059,
        918540078355454674, 145974401587498647, 892232631763653346,
        205368859364249926] : ℤ),
    (decimalNat
      [51183, 519968828061427758, 996246864382530043,
        575936113123996785, 141060160003225697, 424118227101748237,
        600868879260797477] : ℤ),
    -(decimalNat
      [11918, 280617401180183048, 185897305923750552,
        168291558289027807, 607300092317781443, 551596322794185875,
        803947600257118329] : ℤ),
    (decimalNat
      [1330, 132421943487036469, 385187188017008599,
        860775466826773784, 739602058778683384, 946560000000000000,
        0] : ℤ),
    (decimalNat
      [158, 941067201385166633, 771237852077437656,
        196051216047071211, 71872374857239176, 52160000000000000,
        0] : ℤ),
    -(decimalNat
      [103, 786653169533777698, 197952844417839129,
        610468923133699301, 649263653826366776, 661920000000000000,
        0] : ℤ),
    (decimalNat
      [22, 495432778626539101, 274378393697706209,
        519899252165642382, 840505969542273946, 665440000000000000,
        0] : ℤ),
    -(decimalNat
      [2, 611393715623355775, 79499391418550703,
        993058446279335893, 577764555842364569, 887040000000000000,
        0] : ℤ),
    (decimalNat
      [134136049900814276, 368637090262715172, 654619705540887495,
        341013418513505283, 207040000000000000, 0] : ℤ)]

private def plateauBookPowerRound3 : List ℤ → ℝ → ℝ
  | [], _ => 0
  | coefficient :: coefficients, x =>
      coefficient + x * plateauBookPowerRound3 coefficients x

private def plateauBookCoeffsRound3 : List ℕ :=
  [
    decimalNat
      [24255792, 649144966486736329, 833143776172056173,
        88349225991587789, 306957828968072639, 818474232030955474,
        850782598237639726, 515814198338335191, 438630730175329196,
        618727577213228463, 244640531539567308, 201238346897421168,
        24601983380974511, 185304553294050964, 771516357617385472],
    decimalNat
      [1243129100, 175885375459408485, 704580287574702332,
        574380102240139033, 615474323100625034, 869088124351857888,
        989741493671823127, 447911402543894776, 550858608872681581,
        197986338056342941, 44183598664609843, 673742968689867304,
        211698632841414234, 61560262606815764, 201184935995768832],
    decimalNat
      [31237476801, 810618723478054315, 532826817915099703,
        581750310542390822, 484553562386828707, 980336744350115772,
        491318166100476123, 133034067921136455, 391054603353419047,
        511429377045716046, 201769414966793630, 570957372407688360,
        385054392885487390, 194947885291162670, 536050325145518080],
    decimalNat
      [512953454516, 554374621327834841, 732285471702095561,
        994949881266602027, 804385384747151799, 348353216491391887,
        785031001904457907, 56497119228546196, 528913136144164726,
        825654075642005530, 561903908012220929, 18457280998603472,
        744266751734303887, 615187405519184193, 759680241535549440],
    decimalNat
      [6190341031202, 856445071313911656, 281024546242380004,
        326392831579126573, 326028835148757673, 759046363992719218,
        965293898460897807, 289813171762080033, 150637343093953134,
        616403088776106922, 795584697595290093, 760188615551081616,
        7662977371820893, 952698473536651159, 847071977129902080],
    decimalNat
      [58539542164045, 69096728722129480, 748477593436033105,
        595694608330709690, 417681764533805353, 317216976418418803,
        901774542188537779, 108568790288128501, 385407727311016021,
        877889103421704871, 744208946279563301, 9292845766749483,
        879279786431811828, 139245158315350765, 127345182796152832],
    decimalNat
      [451690158460314, 3606142551943127, 898639532472331953,
        880506562684400975, 828856523930733147, 214318858515994641,
        359189411850598659, 458003665745390784, 954619659281875718,
        663719400167641942, 150110936235221620, 18931497150076475,
        87578948736880107, 865218572911410311, 889998786406121472],
    decimalNat
      [2923797664643876, 451434735530736368, 926918401203057783,
        178012628361545586, 365739092719885738, 614068110475940713,
        935078312946928732, 60374528014887315, 53235061600815481,
        260468711783279691, 616839955965555240, 285212644501250127,
        409634511813004866, 486621888773151948, 406020905107456000],
    decimalNat
      [16201048364802129, 533281264808400288, 223521573173701473,
        630873820000477878, 518247052533228326, 584355882051564740,
        213089115672900233, 194804031408198708, 636430614052484591,
        855668536237760324, 79625616833375019, 83076421029788032,
        780935142600365718, 716015048192179474, 528139739136000000],
    decimalNat
      [78033432511523270, 894317862275751126, 950100331454670049,
        454636056432031649, 592138030981289246, 145196872354832215,
        19589337894179164, 23855192569564706, 582616201590627116,
        807722392498808914, 7992116383503754, 359400971918304130,
        767367499797053560, 595361560371652663, 883857920000000000],
    decimalNat
      [330645436886720567, 652788301572919259, 694445979427719607,
        832838686079394527, 157839524694571294, 660512689859927565,
        698294818202230074, 301469586916534941, 835343459933803509,
        201845383086849011, 606450932703775026, 699915782880596083,
        436646251936163816, 377611870858227883, 180032000000000000],
    decimalNat
      [1, 244384958313877661, 494266956724842817,
        426925471065418337, 361071090546885807, 27689090094753950,
        480545086132065155, 712960189092521951, 277075929862331370,
        942073219631350339, 762175476898715902, 127833599426738987,
        265113949765500808, 682418642900459110, 390165571820503171,
        72000000000000000],
    decimalNat
      [4, 192340688572726486, 279996669471905272,
        743265533144224192, 254417875450782641, 462619931278278178,
        706011195797034467, 145234826667082420, 191987007394620415,
        957463752038101351, 54486469942831913, 726773705377013366,
        390113701609720161, 257271510125139528, 449573353768878080,
        0],
    decimalNat
      [12, 725737071152733567, 602208699303327597,
        342976884822611560, 360783773933619009, 526481824431582780,
        761844358504962647, 807946429043810249, 609882973010582625,
        573078272054485744, 940778027278475503, 557432119662990484,
        888631210223452458, 608656243775924538, 837579834851328000,
        0],
    decimalNat
      [34, 993946806833002639, 625788330401052223,
        697203120900612589, 167740442851240160, 651727404750526132,
        541232451402897888, 587292840238207309, 289025990178765987,
        615561676092143128, 370790210586515549, 667873206225020711,
        850707813774853196, 178713639195683563, 660617187328000000,
        0],
    decimalNat
      [87, 575432687194720074, 198489089076208330,
        259191526413214260, 841209224690889291, 231942983673376229,
        156518356728086403, 267937257481658293, 669916164403364789,
        780255675301530475, 144434532030306942, 743123716829941497,
        293262855266981122, 55494703707563651, 181314048000000000,
        0],
    decimalNat
      [200, 240561661872944283, 766954205322731626,
        395252457273805280, 835809725301186116, 797410624625896248,
        451289155500395681, 358365740642645212, 439060759248762393,
        168286913801844339, 95523333783578437, 563833459634302657,
        288943614398310821, 130030163982416418, 439168000000000000,
        0],
    decimalNat
      [419, 720397356205690419, 941495639866381573,
        163265445519875632, 370523883711372070, 843479677353367575,
        486134535240734857, 913923742465694219, 380130372477270516,
        627091290870944164, 254479524513583927, 501402676326117830,
        693467848697805972, 991841831890861424, 640000000000000000,
        0],
    decimalNat
      [808, 836102163075208126, 25428045720763132,
        131276287657992049, 797877401697875666, 631888320860921082,
        458032791297080401, 552249358782346921, 444435514346465941,
        788792031341466347, 857443484830622997, 773957047702252225,
        614123255910946674, 980441864307474432, 0,
        0],
    decimalNat
      [1436, 595245615154944663, 95384887170277691,
        590261431163794255, 291730299744534971, 610102371215526633,
        126843367246770350, 336128145007409859, 394013546364670738,
        135161781442288418, 525766944190442070, 986808441736733604,
        199795853329708616, 161626481754112000, 0,
        0],
    decimalNat
      [2356, 749225225731508910, 592769446884410082,
        377874713141326489, 842227753587716382, 990381501795557052,
        814052474922773705, 882654714682393420, 189813390684387537,
        203303982473208256, 702771780931842189, 90099754066217169,
        632775271282493892, 707252822016000000, 0,
        0],
    decimalNat
      [3577, 651765377985759966, 329807537184353926,
        349316214422228336, 500165321578235667, 865627565068512747,
        783633898261535067, 744657306891887418, 495655430697565933,
        800698157335333119, 989851357278320787, 888084922195034964,
        17278916907922690, 300184320000000000, 0,
        0],
    decimalNat
      [5033, 529029656132407902, 926777005780323933,
        474297058828594421, 124495352314683092, 150263877601422953,
        415892026090958857, 712426653314072660, 893665953696362605,
        872637619236029928, 579577066859041806, 816511870668885769,
        181503076604896809, 544088000000000000, 0,
        0],
    decimalNat
      [6572, 267021070519752064, 814371202595161554,
        94023272955934575, 824059889707457379, 604103374032218514,
        821368015996286628, 841439499144992406, 628100040600824097,
        885607460717557681, 47175371960254373, 878813419967470953,
        436045911987249816, 360750000000000000, 0,
        0],
    decimalNat
      [7972, 716886545722650064, 105182632750121483,
        476812514611662366, 63487174433875820, 183440598877969247,
        720529534382820758, 114349356878523378, 102997246966026402,
        241730843346347188, 775159814354085373, 557470849970064534,
        432290222979396512, 507812500000000000, 0,
        0],
    decimalNat
      [8993, 606285703481577636, 489848749278854779,
        824745871882665013, 220476179763281505, 445243368281546782,
        651609710689220575, 75478826001540311, 380686671062016468,
        573446754825508709, 298087906849514175, 708799185002883195,
        104089870881294877, 197265625000000000, 0,
        0],
    decimalNat
      [9440, 524888740315295235, 848778387024375497,
        305092357347369522, 698165973783256421, 558084508544817554,
        147626273532351048, 760978776335805985, 560232628319746947,
        822149885660044618, 831570411182894348, 737649635306598066,
        81071646794052955, 627441406250000000, 0,
        0],
    decimalNat
      [9225, 776140661524666919, 697938602414949912,
        483426854516922803, 785834199023501509, 872395314950846409,
        498996885310814670, 902285134143916637, 428546731129099262,
        492122015752006636, 339876986010312646, 182834572115905513,
        823818849336608171, 463012695312500000, 0,
        0],
    decimalNat
      [8396, 36001357418240894, 326463958535058133,
        222592829777640239, 38120731647456801, 430948875565857206,
        521946435006069916, 55037897293268676, 819489229646995145,
        441515053403105999, 999072968768322603, 454006361204818754,
        900127787766553461, 551666259765625000, 0,
        0],
    decimalNat
      [7116, 30827664772495760, 880194890841631589,
        935277576657887172, 651673828255470256, 486731332245190651,
        275643219892480291, 423798470983349010, 925689963129854529,
        171436162992073242, 122912407110979026, 538606486820375993,
        794284439933719113, 469123840332031250, 0,
        0],
    decimalNat
      [5615, 957269761066962451, 625941355240186750,
        474999288728590056, 402596522652885711, 394910968539748942,
        174844996384154614, 181790370622739407, 215189579949310954,
        36201429283840874, 74683458154731799, 441754070713309250,
        895466297348320949, 822664260864257812, 500000000000000000,
        0],
    decimalNat
      [4125, 332048607728849643, 101044898281961442,
        501548118859732400, 373223938116074326, 166776821037081845,
        594272393988964492, 283305540702011420, 795581115146901408,
        731191688098713144, 634223830222191439, 54835204300078624,
        133367449985598796, 47270298004150390, 625000000000000000,
        0],
    decimalNat
      [2818, 761223139401414498, 48494037373798318,
        261991266916285392, 348040971085558522, 175318465431348338,
        447179890126593149, 450287229487879204, 697016041899648399,
        423188176464320078, 368214597361229640, 29721289329871543,
        879135327159701773, 780398070812225341, 796875000000000000,
        0],
    decimalNat
      [1789, 846855857111987509, 404863770955158324,
        810580469019554846, 520315183290648692, 11949050882083844,
        231422984308276384, 917346217390805752, 972597357404908351,
        804148448227145428, 483322110769500223, 121804416094046758,
        7949704527561607, 392271980643272399, 902343750000000000,
        0],
    decimalNat
      [1054, 855905972804859617, 982260471269113413,
        156879642124831118, 551748727355458622, 890840919041886018,
        954140552516322545, 475656578813153410, 193347711123756686,
        741739017659920520, 738241992337374470, 744642857423316788,
        618130462884536768, 797261174768209457, 397460937500000000,
        0],
    decimalNat
      [576, 110602789878358201, 810916540231814783,
        527606491559234718, 382216381461660864, 875274760939145082,
        288127508245292462, 406344850994411756, 244494835322759920,
        420781831743915185, 724033549057199511, 632612387325739377,
        745277385034494699, 311835574917495250, 701904296875000000,
        0],
    decimalNat
      [291, 10451819423426692, 227710514535564150,
        19162524406236795, 221728244465231837, 549490616963412850,
        29827908614102795, 346505208434600204, 470738080967696505,
        853876839321219854, 288414903418714124, 5049163570329688,
        487716692998907852, 540924068307504057, 884216308593750000,
        0],
    decimalNat
      [135, 636303001451227202, 401913081166734971,
        67315413079679938, 536526833379487729, 870536810216699011,
        841091452611433812, 672185582095386863, 78819019262926321,
        86168552801641532, 382993356339854567, 336836777834545718,
        391240354521593003, 411794597923289984, 464645385742187500,
        0],
    decimalNat
      [58, 167437688126151484, 790301696687711972,
        424614028716028418, 945425803119635866, 902432350770138653,
        656985146247684456, 483491993715334270, 238975150347820199,
        49488746723950359, 500682650120547649, 538369182832006421,
        800560052519195319, 842282287936541251, 838207244873046875,
        0],
    decimalNat
      [22, 875012982837788809, 41323581991639935,
        579437166001294283, 748408645624309995, 259053210775019538,
        723646670817290847, 461890909215746669, 406100252424468213,
        921911018614013104, 694918178331863141, 275388630683437466,
        348593993355686401, 769411020268307765, 945792198181152343,
        750000000000000000],
    decimalNat
      [8, 216618162253691364, 647385632195934197,
        418230049068841606, 392313901855504612, 45665747325625361,
        937851544190169386, 975508671553477044, 556108371257246947,
        509633131673528725, 67398801391780486, 867258184012947744,
        704763400386455813, 456665353555763431, 359082460403442382,
        812500000000000000],
    decimalNat
      [2, 683070103663456240, 117839743092809969,
        602662768705452055, 96641928326151718, 221363547101059892,
        314860858682646058, 636060056352898622, 623211630925303476,
        547930157358387538, 696099399799279885, 337078670513093909,
        217122996332659267, 716691520178073915, 303684771060943603,
        515625000000000000],
    decimalNat
      [792052689222551983, 643336867270324613, 297542344458936516,
        174888993134814493, 424820202603620487, 447274676086735273,
        303504065349229536, 460896748456515211, 158497215805246132,
        391285276683259867, 391040804970228479, 599328288894732370,
        698306689327239382, 691914215683937072, 753906250000000000],
    decimalNat
      [209974044043593263, 110029065182517626, 173194894668346653,
        953389574596021127, 111891861983105833, 200850529735805908,
        968627279502083368, 688692519530358423, 929697176067461277,
        504986387088492909, 757699176766968227, 133394198953878890,
        493308234654890043, 202613014727830886, 840820312500000000],
    decimalNat
      [49588256575597565, 35406632359869123, 928082966306266782,
        204773117078481427, 435567316575563769, 144141194057180421,
        985440304088006089, 572771085418157995, 897577072246625286,
        292692008890088332, 845919710505473319, 49345389526955955,
        799094634406376513, 879877165891230106, 353759765625000000],
    decimalNat
      [10330767738457021, 959796145848563038, 182556424023102791,
        990915482553363778, 123740395309541306, 314322315218552556,
        122898256838168929, 157228004466388006, 473632167509275382,
        922310222567593495, 345476270005901074, 693746945289273216,
        133453569057221166, 360704955877736210, 823059082031250000],
    decimalNat
      [1875539495645737, 785750032469613721, 500554589183648926,
        312911357660747609, 172003636818233475, 97660105550299642,
        36825679710155869, 583119047180325036, 646199531602980731,
        455962492842913357, 188026791144657055, 125098902543224328,
        557027607861790174, 936800212890375405, 550003051757812500],
    decimalNat
      [292151576923790, 972774855719725356, 74011072437807118,
        807659211659119781, 451109560735739674, 708041746513251448,
        994335302386437927, 356525535836944200, 108956961412849787,
        610017494914995965, 97167023549159991, 842036631477959343,
        937146394058236575, 919096367215388454, 496860504150390625],
    decimalNat
      [38256725470407, 357931530682954933, 720608037003802924,
        580711489946357438, 259758180691699071, 291180667381593973,
        834723317345934712, 866366522027487733, 804085976143926871,
        761313750574388734, 576988704672431225, 491149017822352871,
        572261727830047139, 953251189581351354, 718208312988281250],
    decimalNat
      [4095173659461, 125922658026047463, 796901012728212205,
        346554890695922509, 610014241402348372, 836681604625964310,
        649893269181034049, 513840292892561546, 503137012839739531,
        229824994671629903, 839956073739207692, 850465234913186691,
        931526994792621410, 24224815060733817, 517757415771484375],
    decimalNat
      [344075931722, 476244230810221695, 333275087298403396,
        869680964703495248, 575372206099384528, 268223131470080944,
        811576196630918787, 932092423595024295, 547563326324050805,
        536129790549702424, 114078421121695693, 734495526492329353,
        606661104109099014, 181083475705236196, 517944335937500000],
    decimalNat
      [21276815145, 357200033266026453, 798867958207558882,
        340876296657501886, 937341738437252802, 161723750735584586,
        29862447238351930, 353915121479048677, 255036534826666791,
        659045268289395631, 389064084596545768, 424799027769591947,
        49665717358289673, 821758469784981571, 137905120849609375],
    decimalNat
      [860913471, 113698743568662768, 545269931892931594,
        663785165946898202, 60212927591532951, 522333893673938355,
        169685806881813575, 739748834403712323, 727552038541557485,
        456982989969741746, 471601930998160934, 530762167845103550,
        628791012769638890, 667067698814207687, 973976135253906250],
    decimalNat
      [17098516, 645744945031812578, 722024430110232919,
        729729793003983395, 465779512855361748, 429716922773075832,
        853669296746355882, 883353238086872914, 227569748001377291,
        708840802356765518, 85993962552487223, 4577845364257046,
        686986340013926499, 725727126133278943, 598270416259765625]]

private def homogenizedIntegerPolynomial :
    List ℤ → Polynomial ℤ
  | [] => 0
  | coefficient :: coefficients =>
      (coefficient * 1000 ^ coefficients.length :
          Polynomial ℤ) +
        (268 + 107 * Polynomial.X) *
          homogenizedIntegerPolynomial coefficients

private lemma eval₂_homogenizedIntegerPolynomial
    (coefficients : List ℤ) (x : ℝ) :
    Polynomial.eval₂ (Int.castRingHom ℝ) x
        (homogenizedIntegerPolynomial coefficients) * 1000 =
      1000 ^ coefficients.length *
        plateauBookPowerRound3 coefficients
          ((268 + 107 * x) / 1000) := by
  induction coefficients with
  | nil =>
      simp [homogenizedIntegerPolynomial,
        plateauBookPowerRound3]
  | cons coefficient coefficients ih =>
      simp only [homogenizedIntegerPolynomial,
        plateauBookPowerRound3, List.length_cons,
        Polynomial.eval₂_add, Polynomial.eval₂_mul,
        Polynomial.eval₂_X]
      simp only [Polynomial.eval₂_ofNat] at *
      simp only [← Polynomial.C_eq_intCast,
        Polynomial.eval₂_C, Polynomial.eval₂_pow,
        Polynomial.eval₂_ofNat] at *
      rw [pow_succ]
      field_simp
      linear_combination (268 + 107 * x) * ih

private def plateauBookBernsteinPolynomialRound3 :
    Polynomial ℤ :=
  ∑ i ∈ Finset.range 54,
    (plateauBookCoeffsRound3.getD i 0 : Polynomial ℤ) *
      Polynomial.X ^ i *
        ((1 : Polynomial ℤ) - Polynomial.X) ^ (53 - i)

set_option maxHeartbeats 0 in
-- Exact normalization of the degree-53 polynomial identity exceeds the default heartbeat budget.
set_option maxRecDepth 10000 in
-- The same normalization also exceeds the default simplifier recursion depth.
private lemma plateau_book_polynomial_identity_round3 :
    (10 ^ 141 : Polynomial ℤ) *
        homogenizedIntegerPolynomial
          plateauBookPowerCoeffsRound3 =
      (1000 ^ 53 : Polynomial ℤ) *
        plateauBookBernsteinPolynomialRound3 := by
  norm_num [plateauBookBernsteinPolynomialRound3,
    homogenizedIntegerPolynomial,
    plateauBookPowerCoeffsRound3,
    plateauBookCoeffsRound3, decimalNat,
    Finset.sum_range_succ]
  ring

private def plateauBookDenRound3 (z : ℝ) : ℝ :=
  let B := plateauBlueUpperRound3 z
  let M := plateauMuUpper z
  596836684839187337551744890533500671552000000000000000000000000000000000 *
    (z + 1) ^ 5 * (z + 2) ^ 5 *
    (10000000000 * (1 - B)) *
    (10000000000 * (2 - B)) ^ 3 *
    (24 * (2 - M)) ^ 3 *
    (24 * (1 - M))

set_option maxHeartbeats 0 in
-- Normalizing the exact degree-53 Bernstein identity exceeds the default heartbeat budget.
set_option maxRecDepth 10000 in
-- The expanded identity also exceeds the default simplifier recursion depth.
private lemma plateau_book_lower_round3_pos {z : ℝ}
    (hz : z ∈ Set.Icc (67 / 250 : ℝ) (3 / 8)) :
    0 < plateauBookLower (33 / 1000) (3 / 100)
      plateauBlueUpperRound3 z := by
  let u : ℝ := (1000 * z - 268) / 107
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have hsum := bernstein_sum_pos_of_ends 53
    plateauBookCoeffsRound3 hu (by
      norm_num [plateauBookCoeffsRound3, decimalNat]) (by
      norm_num [plateauBookCoeffsRound3, decimalNat])
  have hzwide : z ∈ Set.Icc (0 : ℝ) (2 / 5) := by
    constructor <;> nlinarith [hz.1, hz.2]
  have hblue := tangent_blue_le_round3 hz
  have hblue0 : 0 ≤ tangentBlue (3 / 100) z := by
    unfold tangentBlue
    exact mul_nonneg hzwide.1 (Real.exp_pos _).le
  have hB0 : 0 ≤ plateauBlueUpperRound3 z :=
    hblue0.trans hblue
  have hz3 : z ^ 3 ≤ (4 / 25 : ℝ) * z := by
    nlinarith [hzwide.1, hzwide.2, sq_nonneg z,
      mul_nonneg (sq_nonneg z) hzwide.1,
      mul_nonneg (sq_nonneg z) (sub_nonneg.mpr hzwide.2)]
  have hB1 : plateauBlueUpperRound3 z < 1 := by
    dsimp [plateauBlueUpperRound3]
    nlinarith [hzwide.1, hzwide.2, hz3, sq_nonneg z,
      pow_nonneg hzwide.1 4]
  have he0 : 0 ≤ plateauExpNegUpper z :=
    (Real.exp_pos (-z)).le.trans (exp_neg_upper_plateau hzwide)
  have he1 : plateauExpNegUpper z ≤ 1 := by
    have hcoef :
        0 ≤ 1 - z / 2 + z ^ 2 / 6 - z ^ 3 / 24 := by
      nlinarith [hzwide.1, hzwide.2, sq_nonneg z,
        mul_nonneg (sq_nonneg z) hzwide.1]
    dsimp [plateauExpNegUpper]
    nlinarith [mul_nonneg hzwide.1 hcoef]
  have hM0 : 0 ≤ plateauMuUpper z := by
    exact mul_nonneg hzwide.1 he0
  have hM1 : plateauMuUpper z < 1 := by
    dsimp [plateauMuUpper]
    nlinarith [mul_le_mul hzwide.2 he1 he0 (by norm_num : (0 : ℝ) ≤ 2 / 5)]
  have hzplus1Pos : 0 < z + 1 := by
    linarith [hzwide.1]
  have hzplus2Pos : 0 < z + 2 := by
    linarith [hzwide.1]
  have hBsub1Pos :
      0 < 1 - plateauBlueUpperRound3 z :=
    sub_pos.mpr hB1
  have hBsub2Pos :
      0 < 2 - plateauBlueUpperRound3 z := by
    linarith
  have hMsub1Pos : 0 < 1 - plateauMuUpper z :=
    sub_pos.mpr hM1
  have hMsub2Pos : 0 < 2 - plateauMuUpper z := by
    linarith
  have hzplus1 := hzplus1Pos.ne'
  have hzplus2 := hzplus2Pos.ne'
  have hBsub1 := hBsub1Pos.ne'
  have hBsub2 := hBsub2Pos.ne'
  have hMsub1 := hMsub1Pos.ne'
  have hMsub2 := hMsub2Pos.ne'
  have hden : 0 < plateauBookDenRound3 z := by
    dsimp [plateauBookDenRound3]
    positivity
  have hid :
      plateauBookLower (33 / 1000) (3 / 100)
          plateauBlueUpperRound3 z =
        ((∑ i ∈ Finset.range 54,
          (plateauBookCoeffsRound3.getD i 0 : ℝ) *
            u ^ i * (1 - u) ^ (53 - i)) /
          10 ^ 141) /
          plateauBookDenRound3 z := by
    dsimp only [plateauBookLower, plateauXLogLower]
    rw [medium_log_lower_three_closed (by
        nlinarith [hzwide.1]),
      medium_log_lower_below_one_sub hB0 hB1,
      medium_log_lower_below_one_sub hM0 hM1,
      medium_log_upper_below_closed (by
        nlinarith [hz.1]) (by
        nlinarith [hzwide.1])]
    apply (eq_div_iff hden.ne').2
    calc
      _ = plateauBookPowerRound3
          plateauBookPowerCoeffsRound3 z := by
        dsimp [plateauLogThreeClosed,
          plateauLogLowerBelowOneSub, plateauSumLower,
          plateauBookDenRound3, mediumLogLowerThree,
          mediumLogLowerBelow, mediumLogUpperBelow,
          mediumLogUpperSix, mediumExpNegLower,
          mediumExpNegUpper, KernelBounds.expNegTaylor9,
          KernelBounds.expNegError10]
        norm_num [Nat.factorial]
        field_simp [hzplus1, hzplus2, hBsub1, hBsub2,
          hMsub1, hMsub2]
        dsimp [plateauMuUpper, plateauExpNegUpper,
          plateauBlueUpperRound3, mediumCorrectionPolynomial]
        rw [show 1 + z + 1 = z + 2 by ring]
        field_simp [hzplus1, hzplus2]
        dsimp [plateauBookPowerRound3,
          plateauBookPowerCoeffsRound3, decimalNat]
        ring
      _ = _ := by
        have hBernstein :
            Polynomial.eval₂ (Int.castRingHom ℝ) u
                plateauBookBernsteinPolynomialRound3 =
              ∑ i ∈ Finset.range 54,
                (plateauBookCoeffsRound3.getD i 0 : ℝ) *
                  u ^ i * (1 - u) ^ (53 - i) := by
          dsimp [plateauBookBernsteinPolynomialRound3]
          change
            (Polynomial.eval₂RingHom (Int.castRingHom ℝ) u)
                (∑ i ∈ Finset.range 54,
                  (plateauBookCoeffsRound3.getD i 0 :
                      Polynomial ℤ) *
                    Polynomial.X ^ i *
                      ((1 : Polynomial ℤ) - Polynomial.X) ^
                        (53 - i)) =
              _
          simp [Polynomial.eval₂_pow]
        have hpoly := congrArg
          (Polynomial.eval₂ (Int.castRingHom ℝ) u)
          plateau_book_polynomial_identity_round3
        have hzFromU :
            ((268 + 107 * u) / 1000 : ℝ) = z := by
          dsimp [u]
          ring
        have hhom :=
          eval₂_homogenizedIntegerPolynomial
            plateauBookPowerCoeffsRound3 u
        change
          Polynomial.eval₂ (Int.castRingHom ℝ) u
                (homogenizedIntegerPolynomial
                  plateauBookPowerCoeffsRound3) *
              1000 =
            1000 ^ 54 *
              plateauBookPowerRound3
                plateauBookPowerCoeffsRound3
                ((268 + 107 * u) / 1000) at hhom
        rw [hzFromU] at hhom
        have hhom' :
            Polynomial.eval₂ (Int.castRingHom ℝ) u
                (homogenizedIntegerPolynomial
                  plateauBookPowerCoeffsRound3) =
              1000 ^ 53 *
                plateauBookPowerRound3
                  plateauBookPowerCoeffsRound3 z := by
          apply mul_right_cancel₀
            (by norm_num : (1000 : ℝ) ≠ 0)
          calc
            _ = 1000 ^ 54 *
                plateauBookPowerRound3
                  plateauBookPowerCoeffsRound3 z := hhom
            _ = _ := by ring
        simp only [Polynomial.eval₂_mul,
          Polynomial.eval₂_pow,
          Polynomial.eval₂_ofNat] at hpoly
        rw [hBernstein] at hpoly
        rw [hhom'] at hpoly
        rw [eq_div_iff (by positivity : (10 : ℝ) ^ 141 ≠ 0)]
        apply mul_left_cancel₀
          (by positivity : (1000 : ℝ) ^ 53 ≠ 0)
        calc
          _ = (10 : ℝ) ^ 141 *
              (1000 ^ 53 *
                plateauBookPowerRound3
                  plateauBookPowerCoeffsRound3 z) := by
            ring
          _ = _ := hpoly
  rw [hid]
  exact div_pos (div_pos hsum (by norm_num)) hden

/-- The book inequality on the third-round plateau. -/
lemma tangent_plateau_book_round3 :
    ∀ z ∈ Set.Icc (67 / 250 : ℝ) (3 / 8),
      0 < tangentCleanBookMargin (3 / 100) z
        (tangentALog (33 / 1000) (99 / 100) +
          tangentBLog (33 / 1000) (99 / 100) -
          tangentXLog (3 / 100) z - Real.log z) := by
  intro z hz
  have hzwide : z ∈ Set.Icc (0 : ℝ) (2 / 5) := by
    constructor <;> nlinarith [hz.1, hz.2]
  have hblue := tangent_blue_le_round3 hz
  have hblue0 : 0 ≤ tangentBlue (3 / 100) z := by
    unfold tangentBlue
    exact mul_nonneg hzwide.1 (Real.exp_pos _).le
  have hB0 : 0 ≤ plateauBlueUpperRound3 z :=
    hblue0.trans hblue
  have hB1 : plateauBlueUpperRound3 z < 1 := by
    have hz3 : z ^ 3 ≤ (4 / 25 : ℝ) * z := by
      nlinarith [hzwide.1, hzwide.2, sq_nonneg z,
        mul_nonneg (sq_nonneg z) hzwide.1,
        mul_nonneg (sq_nonneg z) (sub_nonneg.mpr hzwide.2)]
    dsimp [plateauBlueUpperRound3]
    nlinarith [hzwide.1, hzwide.2, hz3, sq_nonneg z,
      pow_nonneg hzwide.1 4]
  have he0 : 0 ≤ plateauExpNegUpper z :=
    (Real.exp_pos (-z)).le.trans (exp_neg_upper_plateau hzwide)
  have he1 : plateauExpNegUpper z ≤ 1 := by
    have hcoef :
        0 ≤ 1 - z / 2 + z ^ 2 / 6 - z ^ 3 / 24 := by
      nlinarith [hzwide.1, hzwide.2, sq_nonneg z,
        mul_nonneg (sq_nonneg z) hzwide.1]
    dsimp [plateauExpNegUpper]
    nlinarith [mul_nonneg hzwide.1 hcoef]
  have hM0 : 0 ≤ plateauMuUpper z :=
    mul_nonneg hzwide.1 he0
  have hM1 : plateauMuUpper z < 1 := by
    dsimp [plateauMuUpper]
    nlinarith [mul_le_mul hzwide.2 he1 he0 (by norm_num : (0 : ℝ) ≤ 2 / 5)]
  exact (plateau_book_lower_round3_pos hz).trans_le
    (plateau_book_lower_le (by norm_num) (by norm_num)
      hzwide (by nlinarith [hz.1]) hB0 hB1 hblue hM0 hM1)

lemma round1_forward_t_bounds {z : ℝ}
    (hz : z ∈ Set.Icc (1 / 10 : ℝ) (269 / 1000)) :
    0 < r1ForwardTReal z ∧
      r1ForwardTReal z ≤ 1 ∧ z ≤ r1ForwardTReal z := by
  let u : ℝ := (1000 * z - 100) / 169
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have ht := bernstein_sum_pos_of_ends 4
    [274490108077000000000000, 1656031466477740000000000,
      3512144245738230666000000, 3196048280682543117131000,
      995882379923267782033637] hu (by norm_num) (by norm_num)
  have htUpper := KernelBounds.bernstein_sum_nonneg 4
    [725509891923000000000000, 2343968533522260000000000,
      2487855754261769334000000, 803951719317456882869000,
      4117620076732217966363] hu
  have hzt := KernelBounds.bernstein_sum_nonneg 4
    [174490108077000000000000, 1087031466477740000000000,
      2405144245738230666000000, 2289048280682543117131000,
      726882379923267782033637] hu
  have htId :
      r1ForwardTReal z =
        (∑ i ∈ Finset.range 5,
          (([274490108077000000000000, 1656031466477740000000000,
              3512144245738230666000000, 3196048280682543117131000,
              995882379923267782033637].getD i 0 : ℕ) : ℝ) *
            u ^ i * (1 - u) ^ (4 - i)) /
          1000000000000000000000000 := by
    dsimp [u, r1ForwardTReal, tangentLocalPoly,
      tangentRatHorner, TangentAffine.r1ForwardCs]
    norm_num [Finset.sum_range_succ]
    ring
  have htUpperId :
      1 - r1ForwardTReal z =
        (∑ i ∈ Finset.range 5,
          (([725509891923000000000000, 2343968533522260000000000,
              2487855754261769334000000, 803951719317456882869000,
              4117620076732217966363].getD i 0 : ℕ) : ℝ) *
            u ^ i * (1 - u) ^ (4 - i)) /
          1000000000000000000000000 := by
    dsimp [u, r1ForwardTReal, tangentLocalPoly,
      tangentRatHorner, TangentAffine.r1ForwardCs]
    norm_num [Finset.sum_range_succ]
    ring
  have hztId :
      r1ForwardTReal z - z =
        (∑ i ∈ Finset.range 5,
          (([174490108077000000000000, 1087031466477740000000000,
              2405144245738230666000000, 2289048280682543117131000,
              726882379923267782033637].getD i 0 : ℕ) : ℝ) *
            u ^ i * (1 - u) ^ (4 - i)) /
          1000000000000000000000000 := by
    dsimp [u, r1ForwardTReal, tangentLocalPoly,
      tangentRatHorner, TangentAffine.r1ForwardCs]
    norm_num [Finset.sum_range_succ]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [htId]
    exact div_pos ht (by norm_num)
  · rw [← sub_nonneg, htUpperId]
    exact div_nonneg htUpper (by norm_num)
  · rw [← sub_nonneg, hztId]
    exact div_nonneg hzt (by norm_num)

lemma round2_forward_t_bounds {z : ℝ}
    (hz : z ∈ Set.Icc (1 / 10 : ℝ) (67 / 250)) :
    0 < r2ForwardTReal z ∧
      r2ForwardTReal z ≤ 1 ∧ z ≤ r2ForwardTReal z := by
  let u : ℝ := (125 * z - 25 / 2) / 21
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have ht := bernstein_sum_pos_of_ends 4
    [66570230695800781250, 400854479568675781250,
      844650624244846125000, 772820689292345883875,
      242985039272057131259] hu (by norm_num) (by norm_num)
  have htUpper := KernelBounds.bernstein_sum_nonneg 4
    [177570394304199218750, 575708020431324218750,
      620193125755153875000, 203741810707654116125,
      1155585727942868741] hu
  have hzt := KernelBounds.bernstein_sum_nonneg 4
    [42156168195800781250, 262182604568675781250,
      575119374244846125000, 552117564292345883875,
      177555351772057131259] hu
  have htId :
      r2ForwardTReal z =
        (∑ i ∈ Finset.range 5,
          (([66570230695800781250, 400854479568675781250,
              844650624244846125000, 772820689292345883875,
              242985039272057131259].getD i 0 : ℕ) : ℝ) *
            u ^ i * (1 - u) ^ (4 - i)) /
          244140625000000000000 := by
    dsimp [u, r2ForwardTReal, tangentLocalPoly,
      tangentRatHorner, TangentAffine.r2ForwardCs]
    norm_num [Finset.sum_range_succ]
    ring
  have htUpperId :
      1 - r2ForwardTReal z =
        (∑ i ∈ Finset.range 5,
          (([177570394304199218750, 575708020431324218750,
              620193125755153875000, 203741810707654116125,
              1155585727942868741].getD i 0 : ℕ) : ℝ) *
            u ^ i * (1 - u) ^ (4 - i)) /
          244140625000000000000 := by
    dsimp [u, r2ForwardTReal, tangentLocalPoly,
      tangentRatHorner, TangentAffine.r2ForwardCs]
    norm_num [Finset.sum_range_succ]
    ring
  have hztId :
      r2ForwardTReal z - z =
        (∑ i ∈ Finset.range 5,
          (([42156168195800781250, 262182604568675781250,
              575119374244846125000, 552117564292345883875,
              177555351772057131259].getD i 0 : ℕ) : ℝ) *
            u ^ i * (1 - u) ^ (4 - i)) /
          244140625000000000000 := by
    dsimp [u, r2ForwardTReal, tangentLocalPoly,
      tangentRatHorner, TangentAffine.r2ForwardCs]
    norm_num [Finset.sum_range_succ]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [htId]
    exact div_pos ht (by norm_num)
  · rw [← sub_nonneg, htUpperId]
    exact div_nonneg htUpper (by norm_num)
  · rw [← sub_nonneg, hztId]
    exact div_nonneg hzt (by norm_num)

lemma round3_forward_t_bounds {z : ℝ}
    (hz : z ∈ Set.Icc (1 / 10 : ℝ) (67 / 250)) :
    0 < r3ForwardTReal z ∧
      r3ForwardTReal z ≤ 1 ∧ z ≤ r3ForwardTReal z := by
  let u : ℝ := (125 * z - 25 / 2) / 21
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have ht := bernstein_sum_pos_of_ends 4
    [66410746318115234375, 399879211494570312500,
      841161745373765531250, 771128493124562046875,
      243245604505435017518] hu (by norm_num) (by norm_num)
  have htUpper := KernelBounds.bernstein_sum_nonneg 4
    [177729878681884765625, 576683288505429687500,
      623682004626234468750, 205434006875437953125,
      895020494564982482] hu
  have hzt := KernelBounds.bernstein_sum_nonneg 4
    [41996683818115234375, 261207336494570312500,
      571630495373765531250, 550425368124562046875,
      177815917005435017518] hu
  have htId :
      r3ForwardTReal z =
        (∑ i ∈ Finset.range 5,
          (([66410746318115234375, 399879211494570312500,
              841161745373765531250, 771128493124562046875,
              243245604505435017518].getD i 0 : ℕ) : ℝ) *
            u ^ i * (1 - u) ^ (4 - i)) /
          244140625000000000000 := by
    dsimp [u, r3ForwardTReal, tangentLocalPoly,
      tangentRatHorner, TangentAffine.r3ForwardCs]
    norm_num [Finset.sum_range_succ]
    ring
  have htUpperId :
      1 - r3ForwardTReal z =
        (∑ i ∈ Finset.range 5,
          (([177729878681884765625, 576683288505429687500,
              623682004626234468750, 205434006875437953125,
              895020494564982482].getD i 0 : ℕ) : ℝ) *
            u ^ i * (1 - u) ^ (4 - i)) /
          244140625000000000000 := by
    dsimp [u, r3ForwardTReal, tangentLocalPoly,
      tangentRatHorner, TangentAffine.r3ForwardCs]
    norm_num [Finset.sum_range_succ]
    ring
  have hztId :
      r3ForwardTReal z - z =
        (∑ i ∈ Finset.range 5,
          (([41996683818115234375, 261207336494570312500,
              571630495373765531250, 550425368124562046875,
              177815917005435017518].getD i 0 : ℕ) : ℝ) *
            u ^ i * (1 - u) ^ (4 - i)) /
          244140625000000000000 := by
    dsimp [u, r3ForwardTReal, tangentLocalPoly,
      tangentRatHorner, TangentAffine.r3ForwardCs]
    norm_num [Finset.sum_range_succ]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [htId]
    exact div_pos ht (by norm_num)
  · rw [← sub_nonneg, htUpperId]
    exact div_nonneg htUpper (by norm_num)
  · rw [← sub_nonneg, hztId]
    exact div_nonneg hzt (by norm_num)

def forwardBlueUpperRound2 (z : ℝ) : ℝ :=
  -(12676329095 / 10000000000) * z ^ 4 +
    22957271328 / 10000000000 * z ^ 3 -
    4145134433 / 2000000000 * z ^ 2 +
    6525682497 / 5000000000 * z +
    60221 / 250000000

lemma plateau_blue_raw_le_round2_forward {z : ℝ}
    (hz : z ∈ Set.Icc (1 / 10 : ℝ) (67 / 250)) :
    plateauBlueRawUpper (33 / 1000) z ≤
      forwardBlueUpperRound2 z := by
  let u : ℝ := (125 * z - 25 / 2) / 21
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have h := KernelBounds.bernstein_sum_nonneg 21
    [214505978299618585083635480259545147418975830078125,
      1265516872252658052828655854682438075542449951171875,
      3136116655099327762727205845294520258903503417968750,
      42450053213917983600690982100786641240119934082031250,
      459065950981753167489690503739402629435062408447265625,
      2548719331266631456790092731309472583234310150146484375,
      8814415755403834299397921058800198137760162353515625000,
      20994786407175873253465998281419166028499603271484375000,
      36195267888386897663901129852707754698395729064941406250,
      46215444022469466983670188536539901965498924255371093750,
      43978056242485785590158539281594523772706985473632812500,
      31092070402006946763264997608957870456687545776367187500,
      16496042664259797722040186954258992786248634338378906250,
      7399958988268466064986574401323326522184681091308593750,
      4028052181138261870732888435457115837172377978515625000,
      2899643986328661698889493729810169988850997396484375000,
      1845437371849053804152536794953544919756424907978515625,
      829031924315452484378820582557367831994574837227734375,
      241969018015513248584906032189887687895936615613968750,
      41481236980644384946580030372041475884284884756751250,
      3195865360144548087196022278630419756370884334752925,
      1691616127128759409264255256711153701797219133843] hu
  have hid :
      forwardBlueUpperRound2 z -
          plateauBlueRawUpper (33 / 1000) z =
        (∑ i ∈ Finset.range 22,
          ((List.getD
            [214505978299618585083635480259545147418975830078125,
              1265516872252658052828655854682438075542449951171875,
              3136116655099327762727205845294520258903503417968750,
              42450053213917983600690982100786641240119934082031250,
              459065950981753167489690503739402629435062408447265625,
              2548719331266631456790092731309472583234310150146484375,
              8814415755403834299397921058800198137760162353515625000,
              20994786407175873253465998281419166028499603271484375000,
              36195267888386897663901129852707754698395729064941406250,
              46215444022469466983670188536539901965498924255371093750,
              43978056242485785590158539281594523772706985473632812500,
              31092070402006946763264997608957870456687545776367187500,
              16496042664259797722040186954258992786248634338378906250,
              7399958988268466064986574401323326522184681091308593750,
              4028052181138261870732888435457115837172377978515625000,
              2899643986328661698889493729810169988850997396484375000,
              1845437371849053804152536794953544919756424907978515625,
              829031924315452484378820582557367831994574837227734375,
              241969018015513248584906032189887687895936615613968750,
              41481236980644384946580030372041475884284884756751250,
              3195865360144548087196022278630419756370884334752925,
              1691616127128759409264255256711153701797219133843]
            i 0 : ℕ) : ℝ) *
            u ^ i * (1 - u) ^ (21 - i)) /
          145519152283668518066406250000000000000000000000000000000 := by
    dsimp [u, forwardBlueUpperRound2,
      plateauBlueRawUpper, plateauInvOneAddUpper,
      plateauExpPosCoarse, mediumCorrectionPolynomial,
      plateauExpNegUpper]
    norm_num [Finset.sum_range_succ]
    ring
  rw [← sub_nonneg, hid]
  exact div_nonneg h (by norm_num)

lemma tangent_blue_le_round2_forward {z : ℝ}
    (hz : z ∈ Set.Icc (1 / 10 : ℝ) (67 / 250)) :
    tangentBlue (33 / 1000) z ≤ forwardBlueUpperRound2 z := by
  have hzwide : z ∈ Set.Icc (0 : ℝ) (2 / 5) := by
    constructor <;> nlinarith [hz.1, hz.2]
  have hP :
      mediumCorrectionPolynomial (33 / 1000) z ≤ 0 := by
    dsimp [mediumCorrectionPolynomial]
    nlinarith [hzwide.1, hzwide.2, sq_nonneg z,
      mul_nonneg (sq_nonneg z) hzwide.1]
  have hq :
      -mediumCorrectionPolynomial (33 / 1000) z *
          plateauExpNegUpper z ∈ Set.Icc (0 : ℝ) (1 / 5) := by
    have hnegP0 :
        0 ≤ -mediumCorrectionPolynomial (33 / 1000) z := by
      linarith
    have hproduct :
        -mediumCorrectionPolynomial (33 / 1000) z *
            plateauExpNegUpper z ≤ 1 / 5 := by
      let u : ℝ := (125 * z - 25 / 2) / 21
      have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
        dsimp [u]
        constructor <;> nlinarith [hz.1, hz.2]
      have h := KernelBounds.bernstein_sum_nonneg 7
        [204302569580078125, 5671398525146484375,
          29388605195126953125, 69012248928177734375,
          88443938839487109375, 64363431716859988125,
          25099311360602774575, 4089078179841152997] hu
      have hid :
          1 / 5 -
              (-mediumCorrectionPolynomial (33 / 1000) z *
                plateauExpNegUpper z) =
            (∑ i ∈ Finset.range 8,
              (([204302569580078125, 5671398525146484375,
                  29388605195126953125, 69012248928177734375,
                  88443938839487109375, 64363431716859988125,
                  25099311360602774575,
                  4089078179841152997].getD i 0 : ℕ) : ℝ) *
                u ^ i * (1 - u) ^ (7 - i)) /
              48828125000000000000 := by
        dsimp [u, mediumCorrectionPolynomial,
          plateauExpNegUpper]
        norm_num [Finset.sum_range_succ]
        ring
      rw [← sub_nonneg, hid]
      exact div_nonneg h (by norm_num)
    have he0 : 0 ≤ plateauExpNegUpper z :=
      (Real.exp_pos (-z)).le.trans
        (exp_neg_upper_plateau hzwide)
    constructor
    · exact mul_nonneg hnegP0 he0
    · exact hproduct
  exact (tangent_blue_le_plateau_raw hzwide hP hq).trans
    (plateau_blue_raw_le_round2_forward hz)

private def forwardBlueBernsteinCoeffsRound1 : List ℕ :=
  [94350645698421976810846312500000000000000000000000000000000000000,
    2239800970944948932680114430625000000000000000000000000000000000000,
    25151185681656349811645901808343750000000000000000000000000000000000,
    177542554924776124529900250792699687500000000000000000000000000000000,
    883813168597814401362825761110848037500000000000000000000000000000000,
    3300326384327351621908751920892263668225000000000000000000000000000000,
    9601401611089218397486368444377797683507750000000000000000000000000000,
    22308986675352773104330825674351975090013887500000000000000000000000000,
    42098677503776538336838489789831547000528917437500000000000000000000000,
    65247332409098127029973961650251033576301561566875000000000000000000000,
    83638306948705267256430332399513689223242748007691250000000000000000000,
    88988823447232093855075290357408117069538073453842462500000000000000000,
    78619311073939565966617566760195008059782757625704386250000000000000000,
    57517221903645940850721138933020266952280031533796049662500000000000000,
    34629606938452975028470137784557474188412872169682656804875000000000000,
    16980806720760940490110956779093256083849445378646316957029750000000000,
    6673946818126866979391479669371381735628745546187943765335818125000000,
    2052269475131728926920978824689764388607392709906759779285426656250000,
    475678735661033397751314925532440624650272279940713167070645190937500,
    78150957212637850635441251141237962761517988425279523536994740571875,
    8111921315592215118205649221796958494855811001747115751407267338350,
    399927334911948115008012235482639414560119703543134734875227755699]

private lemma plateau_blue_raw_le_round1_forward {z : ℝ}
    (hz : z ∈ Set.Icc (1 / 10 : ℝ) (269 / 1000)) :
    plateauBlueRawUpper (9 / 200) z ≤
      forwardBlueUpperRound2 z := by
  let u : ℝ := (1000 * z - 100) / 169
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have h := KernelBounds.bernstein_sum_nonneg 21
    forwardBlueBernsteinCoeffsRound1 hu
  have hid :
      forwardBlueUpperRound2 z -
          plateauBlueRawUpper (9 / 200) z =
        (∑ i ∈ Finset.range 22,
          (forwardBlueBernsteinCoeffsRound1.getD i 0 : ℝ) *
            u ^ i * (1 - u) ^ (21 - i)) /
          360000000000000000000000000000000000000000000000000000000000000000000 := by
    dsimp [u, forwardBlueUpperRound2,
      plateauBlueRawUpper, plateauInvOneAddUpper,
      plateauExpPosCoarse, mediumCorrectionPolynomial,
      plateauExpNegUpper, forwardBlueBernsteinCoeffsRound1]
    norm_num [Finset.sum_range_succ]
    ring
  rw [← sub_nonneg, hid]
  exact div_nonneg h (by norm_num)

lemma tangent_blue_le_round1_forward {z : ℝ}
    (hz : z ∈ Set.Icc (1 / 10 : ℝ) (269 / 1000)) :
    tangentBlue (9 / 200) z ≤ forwardBlueUpperRound2 z := by
  have hzwide : z ∈ Set.Icc (0 : ℝ) (2 / 5) := by
    constructor <;> nlinarith [hz.1, hz.2]
  have hP :
      mediumCorrectionPolynomial (9 / 200) z ≤ 0 := by
    dsimp [mediumCorrectionPolynomial]
    nlinarith [hzwide.1, hzwide.2, sq_nonneg z,
      mul_nonneg (sq_nonneg z) hzwide.1]
  have hq :
      -mediumCorrectionPolynomial (9 / 200) z *
          plateauExpNegUpper z ∈ Set.Icc (0 : ℝ) (1 / 5) := by
    have hnegP0 :
        0 ≤ -mediumCorrectionPolynomial (9 / 200) z := by
      linarith
    have he0 : 0 ≤ plateauExpNegUpper z :=
      (Real.exp_pos (-z)).le.trans
        (exp_neg_upper_plateau hzwide)
    have hproduct :
        -mediumCorrectionPolynomial (9 / 200) z *
            plateauExpNegUpper z ≤ 1 / 5 := by
      let u : ℝ := (1000 * z - 100) / 169
      have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
        dsimp [u]
        constructor <;> nlinarith [hz.1, hz.2]
      have h := KernelBounds.bernstein_sum_nonneg 7
        [3748287675000000000000, 80437709411500000000000,
          399063811107692500000000, 919872289971617000000000,
          1166456453565996211250000, 842918313956779875695000,
          327025881653103398109475, 53066112787142462265897] hu
      have hid :
          1 / 5 -
              (-mediumCorrectionPolynomial (9 / 200) z *
                plateauExpNegUpper z) =
            (∑ i ∈ Finset.range 8,
              (([3748287675000000000000,
                  80437709411500000000000,
                  399063811107692500000000,
                  919872289971617000000000,
                  1166456453565996211250000,
                  842918313956779875695000,
                  327025881653103398109475,
                  53066112787142462265897].getD i 0 : ℕ) : ℝ) *
                u ^ i * (1 - u) ^ (7 - i)) /
              600000000000000000000000 := by
        dsimp [u, mediumCorrectionPolynomial,
          plateauExpNegUpper]
        norm_num [Finset.sum_range_succ]
        ring
      rw [← sub_nonneg, hid]
      exact div_nonneg h (by norm_num)
    constructor
    · exact mul_nonneg hnegP0 he0
    · exact hproduct
  exact (tangent_blue_le_plateau_raw hzwide hP hq).trans
    (plateau_blue_raw_le_round1_forward hz)

private def forwardBlueBernsteinCoeffsRound3 : List ℕ :=
  [26769635794624589929940384536166675388813018798828125,
    459295550030425699730117294166120700538158416748046875,
    3721477635585258567523542074923170730471611022949218750,
    18926198945252762212287361161579610779881477355957031250,
    67725300931581921985603255147338495589792728424072265625,
    181173805501513857910108329326526797376573085784912109375,
    375762546603144211353686304385077036917209625244140625000,
    618436856828344019055651179129479216039180755615234375000,
    819942686290592177753697137679086301460862159729003906250,
    884092299308143664498215209996173684782385826110839843750,
    779410239661571600973114884825825130607042312622070312500,
    562998777670411581959061301916120650063059616088867187500,
    333033889592038256544976656808634175162563819885253906250,
    160895788719689645389648639354370441314520787048339843750,
    63217477539030533209513542814606949089401336181640625000,
    20100064105942133037885835205271642244249262302734375000,
    5146173690541976893910009129826656684978891874697265625,
    1055322640344802390185296256280250840789716256912109375,
    171359783092315020306316806469280523119665633479218750,
    21245388640915820861664864150624166241616966795831250,
    1812499473357638157982130323260722447109770736298525,
    79204132426556762854939326195278050341294449719067]

private lemma plateau_blue_raw_le_round3_forward {z : ℝ}
    (hz : z ∈ Set.Icc (1 / 10 : ℝ) (67 / 250)) :
    plateauBlueRawUpper (3 / 100) z ≤
      plateauBlueUpperRound3 z := by
  let u : ℝ := (125 * z - 25 / 2) / 21
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have h := KernelBounds.bernstein_sum_nonneg 21
    forwardBlueBernsteinCoeffsRound3 hu
  have hid :
      plateauBlueUpperRound3 z -
          plateauBlueRawUpper (3 / 100) z =
        (∑ i ∈ Finset.range 22,
          (forwardBlueBernsteinCoeffsRound3.getD i 0 : ℝ) *
            u ^ i * (1 - u) ^ (21 - i)) /
          36379788070917129516601562500000000000000000000000000000 := by
    dsimp [u, plateauBlueUpperRound3,
      plateauBlueRawUpper, plateauInvOneAddUpper,
      plateauExpPosCoarse, mediumCorrectionPolynomial,
      plateauExpNegUpper, forwardBlueBernsteinCoeffsRound3]
    norm_num [Finset.sum_range_succ]
    ring
  rw [← sub_nonneg, hid]
  exact div_nonneg h (by norm_num)

lemma tangent_blue_le_round3_forward {z : ℝ}
    (hz : z ∈ Set.Icc (1 / 10 : ℝ) (67 / 250)) :
    tangentBlue (3 / 100) z ≤ plateauBlueUpperRound3 z := by
  have hzwide : z ∈ Set.Icc (0 : ℝ) (2 / 5) := by
    constructor <;> nlinarith [hz.1, hz.2]
  have hP :
      mediumCorrectionPolynomial (3 / 100) z ≤ 0 := by
    dsimp [mediumCorrectionPolynomial]
    nlinarith [hzwide.1, hzwide.2, sq_nonneg z,
      mul_nonneg (sq_nonneg z) hzwide.1]
  have hq :
      -mediumCorrectionPolynomial (3 / 100) z *
          plateauExpNegUpper z ∈ Set.Icc (0 : ℝ) (1 / 5) := by
    have hnegP0 :
        0 ≤ -mediumCorrectionPolynomial (3 / 100) z := by
      linarith
    have he0 : 0 ≤ plateauExpNegUpper z :=
      (Real.exp_pos (-z)).le.trans
        (exp_neg_upper_plateau hzwide)
    have hproduct :
        -mediumCorrectionPolynomial (3 / 100) z *
            plateauExpNegUpper z ≤ 1 / 5 := by
      let u : ℝ := (125 * z - 25 / 2) / 21
      have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
        dsimp [u]
        constructor <;> nlinarith [hz.1, hz.2]
      have h := KernelBounds.bernstein_sum_nonneg 7
        [89559552001953125, 2729631797607421875,
          14327383766923828125, 33821244432513671875,
          43471040639970234375, 31695604782687680625,
          12377031303368758775, 2018533942070222361] hu
      have hid :
          1 / 5 -
              (-mediumCorrectionPolynomial (3 / 100) z *
                plateauExpNegUpper z) =
            (∑ i ∈ Finset.range 8,
              (([89559552001953125, 2729631797607421875,
                  14327383766923828125, 33821244432513671875,
                  43471040639970234375, 31695604782687680625,
                  12377031303368758775,
                  2018533942070222361].getD i 0 : ℕ) : ℝ) *
                u ^ i * (1 - u) ^ (7 - i)) /
              24414062500000000000 := by
        dsimp [u, mediumCorrectionPolynomial,
          plateauExpNegUpper]
        norm_num [Finset.sum_range_succ]
        ring
      rw [← sub_nonneg, hid]
      exact div_nonneg h (by norm_num)
    constructor
    · exact mul_nonneg hnegP0 he0
    · exact hproduct
  exact (tangent_blue_le_plateau_raw hzwide hP hq).trans
    (plateau_blue_raw_le_round3_forward hz)

def forwardExpNegErrorFive (t : ℝ) : ℝ :=
  t ^ 5 / 100

def forwardCorrectionUpperRound2 (t : ℝ) : ℝ :=
  mediumCorrectionPolynomial (9 / 200) t *
      plateauExpNegUpper t +
    3 / 10 * forwardExpNegErrorFive t

lemma correction_slope_le_forward_round2 {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    tangentCorrectionSlope (9 / 200) t ≤
      forwardCorrectionUpperRound2 t := by
  let P := mediumCorrectionPolynomial (9 / 200) t
  let A := plateauExpNegUpper t
  let E := forwardExpNegErrorFive t
  have ht3 : t ^ 3 ≤ t := by
    nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr ht.2),
      mul_nonneg (sq_nonneg t) ht.1,
      mul_nonneg (sq_nonneg t) (sub_nonneg.mpr ht.2)]
  have hP : |P| ≤ (3 / 10 : ℝ) := by
    rw [abs_le]
    dsimp [P, mediumCorrectionPolynomial]
    constructor
    · nlinarith [ht.1, ht3, sq_nonneg t]
    · nlinarith [ht.1, ht.2,
        mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]
  have happrox :
      |Real.exp (-t) - A| ≤ E := by
    have h := Real.exp_bound (x := -t) (n := 5) (by
      rw [abs_neg, abs_of_nonneg ht.1]
      exact ht.2) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial,
      abs_neg, abs_of_nonneg ht.1, A,
      plateauExpNegUpper, E,
      forwardExpNegErrorFive] at h ⊢
    convert h using 1 <;> ring_nf
  have hE : 0 ≤ E := by
    dsimp [E, forwardExpNegErrorFive]
    exact div_nonneg (pow_nonneg ht.1 5) (by norm_num)
  have herror :
      P * (Real.exp (-t) - A) ≤ 3 / 10 * E := by
    calc
      P * (Real.exp (-t) - A) ≤
          |P * (Real.exp (-t) - A)| :=
        le_abs_self _
      _ = |P| * |Real.exp (-t) - A| := abs_mul _ _
      _ ≤ (3 / 10 : ℝ) * E :=
        mul_le_mul hP happrox (abs_nonneg _) (by norm_num)
  calc
    tangentCorrectionSlope (9 / 200) t =
        P * Real.exp (-t) := by
      rfl
    _ = P * A + P * (Real.exp (-t) - A) := by
      ring
    _ ≤ P * A + 3 / 10 * E :=
      by
        simpa [add_comm] using
          add_le_add_left herror (P * A)
    _ = forwardCorrectionUpperRound2 t := by
      rfl

def forwardLogOneAddUpperRound2 (t : ℝ) : ℝ :=
  693149 / 1000000 + (t - 1) / 2

lemma log_one_add_le_forward_round2 {t : ℝ}
    (ht : 0 ≤ t) :
    Real.log (1 + t) ≤ forwardLogOneAddUpperRound2 t := by
  have hratio : 0 < (1 + t) / 2 := by positivity
  have hlogRatio :=
    Real.log_le_sub_one_of_pos hratio
  have hlogTwo := medium_log_upper_six
    (x := (2 : ℝ)) (by norm_num)
  have hlogTwoRat :
      Real.log 2 ≤ (693149 / 1000000 : ℝ) := by
    apply hlogTwo.trans
    norm_num [mediumLogUpperSix]
  rw [show 1 + t = 2 * ((1 + t) / 2) by ring,
    Real.log_mul (by norm_num) hratio.ne']
  dsimp [forwardLogOneAddUpperRound2]
  nlinarith

def forwardBookLowerRound2 (z : ℝ) : ℝ :=
  let t := r2ForwardTReal z
  let B := forwardBlueUpperRound2 z
  (1 + z) * mediumLogLowerThree (1 + z) +
    (-(1 / 4) * z + 33 / 1000 * z ^ 2 +
        2 / 25 * z ^ 3) * plateauExpNegUpper z +
    (plateauXLogLower B z - z ^ 2 +
      z * (mediumLogLowerThree (t / z) -
        forwardLogOneAddUpperRound2 t -
        forwardCorrectionUpperRound2 t)) / 2

lemma forward_book_lower_round2_le {z : ℝ}
    (hz : z ∈ Set.Icc (1 / 10 : ℝ) (67 / 250)) :
    forwardBookLowerRound2 z ≤
      tangentCleanBookMargin (33 / 1000) z
        (tangentBLog (9 / 200) (r2ForwardTReal z) -
          Real.log z) := by
  have hzwide : z ∈ Set.Icc (0 : ℝ) (2 / 5) := by
    constructor <;> nlinarith [hz.1, hz.2]
  have hzunit : z ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hz.1, hz.2]
  have hz0 : 0 < z := by nlinarith [hz.1]
  obtain ⟨ht0, ht1, hzt⟩ := round2_forward_t_bounds hz
  have ht : r2ForwardTReal z ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨ht0.le, ht1⟩
  have hratio :
      (1 : ℝ) ≤ r2ForwardTReal z / z := by
    exact (one_le_div₀ hz0).mpr hzt
  have hlogRatio := medium_log_lower_three hratio
  rw [Real.log_div ht0.ne' hz0.ne'] at hlogRatio
  have hlogAdd := log_one_add_le_forward_round2 ht0.le
  have hcorrection :=
    correction_slope_le_forward_round2 ht
  have hy :
      mediumLogLowerThree (r2ForwardTReal z / z) -
          forwardLogOneAddUpperRound2 (r2ForwardTReal z) -
          forwardCorrectionUpperRound2 (r2ForwardTReal z) ≤
        tangentBLog (9 / 200) (r2ForwardTReal z) -
          Real.log z := by
    unfold tangentBLog
    linarith
  have hblue := tangent_blue_le_round2_forward hz
  have hblue0 : 0 ≤ tangentBlue (33 / 1000) z := by
    unfold tangentBlue
    exact mul_nonneg hzwide.1 (Real.exp_pos _).le
  have hB0 : 0 ≤ forwardBlueUpperRound2 z :=
    hblue0.trans hblue
  have hB1 : forwardBlueUpperRound2 z < 1 := by
    have hz2 : z ^ 2 ≤ (2 / 5 : ℝ) * z := by
      nlinarith [mul_nonneg hzwide.1
        (sub_nonneg.mpr hzwide.2)]
    have hz3 : z ^ 3 ≤ (4 / 25 : ℝ) * z := by
      nlinarith [hzwide.1, hzwide.2, sq_nonneg z,
        mul_nonneg (sq_nonneg z) hzwide.1,
        mul_nonneg (sq_nonneg z)
          (sub_nonneg.mpr hzwide.2)]
    dsimp [forwardBlueUpperRound2]
    nlinarith [hzwide.1, hzwide.2, hz2, hz3,
      pow_nonneg hzwide.1 4]
  have he0 : 0 ≤ plateauExpNegUpper z :=
    (Real.exp_pos (-z)).le.trans
      (exp_neg_upper_plateau hzwide)
  have he1 : plateauExpNegUpper z ≤ 1 := by
    have hcoef :
        0 ≤ 1 - z / 2 + z ^ 2 / 6 - z ^ 3 / 24 := by
      nlinarith [hzwide.1, hzwide.2, sq_nonneg z,
        mul_nonneg (sq_nonneg z) hzwide.1]
    dsimp [plateauExpNegUpper]
    nlinarith [mul_nonneg hzwide.1 hcoef]
  have hM0 : 0 ≤ plateauMuUpper z :=
    mul_nonneg hzwide.1 he0
  have hM1 : plateauMuUpper z < 1 := by
    dsimp [plateauMuUpper]
    nlinarith [mul_le_mul hzwide.2 he1 he0
      (by norm_num : (0 : ℝ) ≤ 2 / 5)]
  have hM := optimizationM_le_plateau_mu hzwide
  have hX := tangent_xlog_lower_of_upper_bounds
    (β := (33 / 1000 : ℝ)) (z := z)
    (B := forwardBlueUpperRound2 z)
    (M := plateauMuUpper z) (by norm_num) hzunit
    hB0 hM0 hblue hM hB1 hM1
  change plateauXLogLower (forwardBlueUpperRound2 z) z ≤
    tangentXLog (33 / 1000) z at hX
  have hentropy := medium_log_lower_three
    (show (1 : ℝ) ≤ 1 + z by linarith [hzwide.1])
  have hP :
      -(1 / 4) * z + 33 / 1000 * z ^ 2 +
          2 / 25 * z ^ 3 ≤ 0 := by
    nlinarith [hzwide.1, hzwide.2, sq_nonneg z,
      mul_nonneg (sq_nonneg z) hzwide.1]
  have hramsey :
      (-(1 / 4) * z + 33 / 1000 * z ^ 2 +
          2 / 25 * z ^ 3) * plateauExpNegUpper z ≤
        ramseyCorrection (33 / 1000) z := by
    unfold ramseyCorrection
    exact mul_le_mul_of_nonpos_left
      (exp_neg_upper_plateau hzwide) hP
  unfold tangentCleanBookMargin
  dsimp [forwardBookLowerRound2]
  nlinarith [mul_le_mul_of_nonneg_left hentropy
      (show (0 : ℝ) ≤ 1 + z by linarith [hzwide.1]),
    mul_le_mul_of_nonneg_left hy hzwide.1]


def forwardCorrectionUpperRound1 (t : ℝ) : ℝ :=
  mediumCorrectionPolynomial (2 / 25) t *
      plateauExpNegUpper t +
    3 / 10 * forwardExpNegErrorFive t

lemma correction_slope_le_forward_round1 {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    tangentCorrectionSlope (2 / 25) t ≤
      forwardCorrectionUpperRound1 t := by
  let P := mediumCorrectionPolynomial (2 / 25) t
  let A := plateauExpNegUpper t
  let E := forwardExpNegErrorFive t
  have ht3 : t ^ 3 ≤ t := by
    nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr ht.2),
      mul_nonneg (sq_nonneg t) ht.1,
      mul_nonneg (sq_nonneg t) (sub_nonneg.mpr ht.2)]
  have hP : |P| ≤ (3 / 10 : ℝ) := by
    rw [abs_le]
    dsimp [P, mediumCorrectionPolynomial]
    constructor
    · nlinarith [ht.1, ht3, sq_nonneg t]
    · nlinarith [ht.1, ht.2,
        mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]
  have happrox :
      |Real.exp (-t) - A| ≤ E := by
    have h := Real.exp_bound (x := -t) (n := 5) (by
      rw [abs_neg, abs_of_nonneg ht.1]
      exact ht.2) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial,
      abs_neg, abs_of_nonneg ht.1, A,
      plateauExpNegUpper, E,
      forwardExpNegErrorFive] at h ⊢
    convert h using 1 <;> ring_nf
  have hE : 0 ≤ E := by
    dsimp [E, forwardExpNegErrorFive]
    exact div_nonneg (pow_nonneg ht.1 5) (by norm_num)
  have herror :
      P * (Real.exp (-t) - A) ≤ 3 / 10 * E := by
    calc
      P * (Real.exp (-t) - A) ≤
          |P * (Real.exp (-t) - A)| :=
        le_abs_self _
      _ = |P| * |Real.exp (-t) - A| := abs_mul _ _
      _ ≤ (3 / 10 : ℝ) * E :=
        mul_le_mul hP happrox (abs_nonneg _) (by norm_num)
  calc
    tangentCorrectionSlope (2 / 25) t =
        P * Real.exp (-t) := by
      rfl
    _ = P * A + P * (Real.exp (-t) - A) := by
      ring
    _ ≤ P * A + 3 / 10 * E :=
      by
        simpa [add_comm] using
          add_le_add_left herror (P * A)
    _ = forwardCorrectionUpperRound1 t := by
      rfl

def forwardBookLowerRound1 (z : ℝ) : ℝ :=
  let t := r1ForwardTReal z
  let B := forwardBlueUpperRound2 z
  (1 + z) * mediumLogLowerThree (1 + z) +
    (-(1 / 4) * z + 9 / 200 * z ^ 2 +
        2 / 25 * z ^ 3) * plateauExpNegUpper z +
    (plateauXLogLower B z - z ^ 2 +
      z * (mediumLogLowerThree (t / z) -
        forwardLogOneAddUpperRound2 t -
        forwardCorrectionUpperRound1 t)) / 2

lemma forward_book_lower_round1_le {z : ℝ}
    (hz : z ∈ Set.Icc (1 / 10 : ℝ) (269 / 1000)) :
    forwardBookLowerRound1 z ≤
      tangentCleanBookMargin (9 / 200) z
        (tangentBLog (2 / 25) (r1ForwardTReal z) -
          Real.log z) := by
  have hzwide : z ∈ Set.Icc (0 : ℝ) (2 / 5) := by
    constructor <;> nlinarith [hz.1, hz.2]
  have hzunit : z ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hz.1, hz.2]
  have hz0 : 0 < z := by nlinarith [hz.1]
  obtain ⟨ht0, ht1, hzt⟩ := round1_forward_t_bounds hz
  have ht : r1ForwardTReal z ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨ht0.le, ht1⟩
  have hratio :
      (1 : ℝ) ≤ r1ForwardTReal z / z := by
    exact (one_le_div₀ hz0).mpr hzt
  have hlogRatio := medium_log_lower_three hratio
  rw [Real.log_div ht0.ne' hz0.ne'] at hlogRatio
  have hlogAdd := log_one_add_le_forward_round2 ht0.le
  have hcorrection :=
    correction_slope_le_forward_round1 ht
  have hy :
      mediumLogLowerThree (r1ForwardTReal z / z) -
          forwardLogOneAddUpperRound2 (r1ForwardTReal z) -
          forwardCorrectionUpperRound1 (r1ForwardTReal z) ≤
        tangentBLog (2 / 25) (r1ForwardTReal z) -
          Real.log z := by
    unfold tangentBLog
    linarith
  have hblue := tangent_blue_le_round1_forward hz
  have hblue0 : 0 ≤ tangentBlue (9 / 200) z := by
    unfold tangentBlue
    exact mul_nonneg hzwide.1 (Real.exp_pos _).le
  have hB0 : 0 ≤ forwardBlueUpperRound2 z :=
    hblue0.trans hblue
  have hB1 : forwardBlueUpperRound2 z < 1 := by
    have hz2 : z ^ 2 ≤ (2 / 5 : ℝ) * z := by
      nlinarith [mul_nonneg hzwide.1
        (sub_nonneg.mpr hzwide.2)]
    have hz3 : z ^ 3 ≤ (4 / 25 : ℝ) * z := by
      nlinarith [hzwide.1, hzwide.2, sq_nonneg z,
        mul_nonneg (sq_nonneg z) hzwide.1,
        mul_nonneg (sq_nonneg z)
          (sub_nonneg.mpr hzwide.2)]
    dsimp [forwardBlueUpperRound2]
    nlinarith [hzwide.1, hzwide.2, hz2, hz3,
      pow_nonneg hzwide.1 4]
  have he0 : 0 ≤ plateauExpNegUpper z :=
    (Real.exp_pos (-z)).le.trans
      (exp_neg_upper_plateau hzwide)
  have he1 : plateauExpNegUpper z ≤ 1 := by
    have hcoef :
        0 ≤ 1 - z / 2 + z ^ 2 / 6 - z ^ 3 / 24 := by
      nlinarith [hzwide.1, hzwide.2, sq_nonneg z,
        mul_nonneg (sq_nonneg z) hzwide.1]
    dsimp [plateauExpNegUpper]
    nlinarith [mul_nonneg hzwide.1 hcoef]
  have hM0 : 0 ≤ plateauMuUpper z :=
    mul_nonneg hzwide.1 he0
  have hM1 : plateauMuUpper z < 1 := by
    dsimp [plateauMuUpper]
    nlinarith [mul_le_mul hzwide.2 he1 he0
      (by norm_num : (0 : ℝ) ≤ 2 / 5)]
  have hM := optimizationM_le_plateau_mu hzwide
  have hX := tangent_xlog_lower_of_upper_bounds
    (β := (9 / 200 : ℝ)) (z := z)
    (B := forwardBlueUpperRound2 z)
    (M := plateauMuUpper z) (by norm_num) hzunit
    hB0 hM0 hblue hM hB1 hM1
  change plateauXLogLower (forwardBlueUpperRound2 z) z ≤
    tangentXLog (9 / 200) z at hX
  have hentropy := medium_log_lower_three
    (show (1 : ℝ) ≤ 1 + z by linarith [hzwide.1])
  have hP :
      -(1 / 4) * z + 9 / 200 * z ^ 2 +
          2 / 25 * z ^ 3 ≤ 0 := by
    nlinarith [hzwide.1, hzwide.2, sq_nonneg z,
      mul_nonneg (sq_nonneg z) hzwide.1]
  have hramsey :
      (-(1 / 4) * z + 9 / 200 * z ^ 2 +
          2 / 25 * z ^ 3) * plateauExpNegUpper z ≤
        ramseyCorrection (9 / 200) z := by
    unfold ramseyCorrection
    exact mul_le_mul_of_nonpos_left
      (exp_neg_upper_plateau hzwide) hP
  unfold tangentCleanBookMargin
  dsimp [forwardBookLowerRound1]
  nlinarith [mul_le_mul_of_nonneg_left hentropy
      (show (0 : ℝ) ≤ 1 + z by linarith [hzwide.1]),
    mul_le_mul_of_nonneg_left hy hzwide.1]


def forwardCorrectionUpperRound3 (t : ℝ) : ℝ :=
  mediumCorrectionPolynomial (33 / 1000) t *
      plateauExpNegUpper t +
    3 / 10 * forwardExpNegErrorFive t

lemma correction_slope_le_forward_round3 {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    tangentCorrectionSlope (33 / 1000) t ≤
      forwardCorrectionUpperRound3 t := by
  let P := mediumCorrectionPolynomial (33 / 1000) t
  let A := plateauExpNegUpper t
  let E := forwardExpNegErrorFive t
  have ht3 : t ^ 3 ≤ t := by
    nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr ht.2),
      mul_nonneg (sq_nonneg t) ht.1,
      mul_nonneg (sq_nonneg t) (sub_nonneg.mpr ht.2)]
  have hP : |P| ≤ (3 / 10 : ℝ) := by
    rw [abs_le]
    dsimp [P, mediumCorrectionPolynomial]
    constructor
    · nlinarith [ht.1, ht3, sq_nonneg t]
    · nlinarith [ht.1, ht.2,
        mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]
  have happrox :
      |Real.exp (-t) - A| ≤ E := by
    have h := Real.exp_bound (x := -t) (n := 5) (by
      rw [abs_neg, abs_of_nonneg ht.1]
      exact ht.2) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial,
      abs_neg, abs_of_nonneg ht.1, A,
      plateauExpNegUpper, E,
      forwardExpNegErrorFive] at h ⊢
    convert h using 1 <;> ring_nf
  have hE : 0 ≤ E := by
    dsimp [E, forwardExpNegErrorFive]
    exact div_nonneg (pow_nonneg ht.1 5) (by norm_num)
  have herror :
      P * (Real.exp (-t) - A) ≤ 3 / 10 * E := by
    calc
      P * (Real.exp (-t) - A) ≤
          |P * (Real.exp (-t) - A)| :=
        le_abs_self _
      _ = |P| * |Real.exp (-t) - A| := abs_mul _ _
      _ ≤ (3 / 10 : ℝ) * E :=
        mul_le_mul hP happrox (abs_nonneg _) (by norm_num)
  calc
    tangentCorrectionSlope (33 / 1000) t =
        P * Real.exp (-t) := by
      rfl
    _ = P * A + P * (Real.exp (-t) - A) := by
      ring
    _ ≤ P * A + 3 / 10 * E :=
      by
        simpa [add_comm] using
          add_le_add_left herror (P * A)
    _ = forwardCorrectionUpperRound3 t := by
      rfl

def forwardBookLowerRound3 (z : ℝ) : ℝ :=
  let t := r3ForwardTReal z
  let B := plateauBlueUpperRound3 z
  (1 + z) * mediumLogLowerThree (1 + z) +
    (-(1 / 4) * z + 3 / 100 * z ^ 2 +
        2 / 25 * z ^ 3) * plateauExpNegUpper z +
    (plateauXLogLower B z - z ^ 2 +
      z * (mediumLogLowerThree (t / z) -
        forwardLogOneAddUpperRound2 t -
        forwardCorrectionUpperRound3 t)) / 2

lemma forward_book_lower_round3_le {z : ℝ}
    (hz : z ∈ Set.Icc (1 / 10 : ℝ) (67 / 250)) :
    forwardBookLowerRound3 z ≤
      tangentCleanBookMargin (3 / 100) z
        (tangentBLog (33 / 1000) (r3ForwardTReal z) -
          Real.log z) := by
  have hzwide : z ∈ Set.Icc (0 : ℝ) (2 / 5) := by
    constructor <;> nlinarith [hz.1, hz.2]
  have hzunit : z ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hz.1, hz.2]
  have hz0 : 0 < z := by nlinarith [hz.1]
  obtain ⟨ht0, ht1, hzt⟩ := round3_forward_t_bounds hz
  have ht : r3ForwardTReal z ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨ht0.le, ht1⟩
  have hratio :
      (1 : ℝ) ≤ r3ForwardTReal z / z := by
    exact (one_le_div₀ hz0).mpr hzt
  have hlogRatio := medium_log_lower_three hratio
  rw [Real.log_div ht0.ne' hz0.ne'] at hlogRatio
  have hlogAdd := log_one_add_le_forward_round2 ht0.le
  have hcorrection :=
    correction_slope_le_forward_round3 ht
  have hy :
      mediumLogLowerThree (r3ForwardTReal z / z) -
          forwardLogOneAddUpperRound2 (r3ForwardTReal z) -
          forwardCorrectionUpperRound3 (r3ForwardTReal z) ≤
        tangentBLog (33 / 1000) (r3ForwardTReal z) -
          Real.log z := by
    unfold tangentBLog
    linarith
  have hblue := tangent_blue_le_round3_forward hz
  have hblue0 : 0 ≤ tangentBlue (3 / 100) z := by
    unfold tangentBlue
    exact mul_nonneg hzwide.1 (Real.exp_pos _).le
  have hB0 : 0 ≤ plateauBlueUpperRound3 z :=
    hblue0.trans hblue
  have hB1 : plateauBlueUpperRound3 z < 1 := by
    have hz2 : z ^ 2 ≤ (2 / 5 : ℝ) * z := by
      nlinarith [mul_nonneg hzwide.1
        (sub_nonneg.mpr hzwide.2)]
    have hz3 : z ^ 3 ≤ (4 / 25 : ℝ) * z := by
      nlinarith [hzwide.1, hzwide.2, sq_nonneg z,
        mul_nonneg (sq_nonneg z) hzwide.1,
        mul_nonneg (sq_nonneg z)
          (sub_nonneg.mpr hzwide.2)]
    dsimp [plateauBlueUpperRound3]
    nlinarith [hzwide.1, hzwide.2, hz2, hz3,
      pow_nonneg hzwide.1 4]
  have he0 : 0 ≤ plateauExpNegUpper z :=
    (Real.exp_pos (-z)).le.trans
      (exp_neg_upper_plateau hzwide)
  have he1 : plateauExpNegUpper z ≤ 1 := by
    have hcoef :
        0 ≤ 1 - z / 2 + z ^ 2 / 6 - z ^ 3 / 24 := by
      nlinarith [hzwide.1, hzwide.2, sq_nonneg z,
        mul_nonneg (sq_nonneg z) hzwide.1]
    dsimp [plateauExpNegUpper]
    nlinarith [mul_nonneg hzwide.1 hcoef]
  have hM0 : 0 ≤ plateauMuUpper z :=
    mul_nonneg hzwide.1 he0
  have hM1 : plateauMuUpper z < 1 := by
    dsimp [plateauMuUpper]
    nlinarith [mul_le_mul hzwide.2 he1 he0
      (by norm_num : (0 : ℝ) ≤ 2 / 5)]
  have hM := optimizationM_le_plateau_mu hzwide
  have hX := tangent_xlog_lower_of_upper_bounds
    (β := (3 / 100 : ℝ)) (z := z)
    (B := plateauBlueUpperRound3 z)
    (M := plateauMuUpper z) (by norm_num) hzunit
    hB0 hM0 hblue hM hB1 hM1
  change plateauXLogLower (plateauBlueUpperRound3 z) z ≤
    tangentXLog (3 / 100) z at hX
  have hentropy := medium_log_lower_three
    (show (1 : ℝ) ≤ 1 + z by linarith [hzwide.1])
  have hP :
      -(1 / 4) * z + 3 / 100 * z ^ 2 +
          2 / 25 * z ^ 3 ≤ 0 := by
    nlinarith [hzwide.1, hzwide.2, sq_nonneg z,
      mul_nonneg (sq_nonneg z) hzwide.1]
  have hramsey :
      (-(1 / 4) * z + 3 / 100 * z ^ 2 +
          2 / 25 * z ^ 3) * plateauExpNegUpper z ≤
        ramseyCorrection (3 / 100) z := by
    unfold ramseyCorrection
    exact mul_le_mul_of_nonpos_left
      (exp_neg_upper_plateau hzwide) hP
  unfold tangentCleanBookMargin
  dsimp [forwardBookLowerRound3]
  nlinarith [mul_le_mul_of_nonneg_left hentropy
      (show (0 : ℝ) ≤ 1 + z by linarith [hzwide.1]),
    mul_le_mul_of_nonneg_left hy hzwide.1]




end

end Arxiv2407_19026
