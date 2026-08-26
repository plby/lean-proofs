import ErdosProblems.Erdos67b.MRFiniteHalaszGaussianSchur

/-!
# Uniform geometric bound for the finite Halász Schur shells

At the shifted line `sigma > 1`, the dyadic Schur shells form a genuine
geometric series.  This file retains that decay instead of paying the number
of shells.  The resulting bound is uniform in the finite prefix and can
therefore be passed through the countable positive-pair limit.
-/

open scoped BigOperators

namespace Erdos67b.MRHalaszBands

private lemma two_pow_rpow_neg_eq (j : ℕ) (epsilon : ℝ) :
    (((2 ^ j : ℕ) : ℝ) ^ (-epsilon)) =
      ((2 : ℝ) ^ (-epsilon)) ^ j := by
  push_cast
  rw [← Real.rpow_natCast_mul (show (0 : ℝ) ≤ 2 by norm_num)]
  rw [mul_comm]
  exact Real.rpow_mul_natCast
    (show (0 : ℝ) ≤ 2 by norm_num) (-epsilon) j

private lemma sum_geometric_le_inv_one_sub
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (J : ℕ) :
    (∑ j ∈ Finset.range J, q ^ j) ≤ (1 - q)⁻¹ := by
  have hs := summable_geometric_of_lt_one hq0 hq1
  exact
    (hs.sum_le_tsum (Finset.range J)
      (fun i _hi ↦ pow_nonneg hq0 i)).trans_eq
        (tsum_geometric_of_lt_one hq0 hq1)

lemma dyadic_weight_rpow_neg_le_geometric
    {L j : ℕ} (hL : 0 < L) {sigma : ℝ} (hsigma : 1 < sigma) :
    (((2 ^ j * L : ℕ) : ℝ) ^ (-sigma)) ≤
      (((2 ^ j * L : ℕ) : ℝ)⁻¹) *
        (((2 : ℝ) ^ (-(sigma - 1))) ^ j) := by
  let Lj : ℝ := ((2 ^ j * L : ℕ) : ℝ)
  have hLj : 0 < Lj := by dsimp [Lj]; positivity
  have hsplit : Lj ^ (-sigma) = Lj⁻¹ * Lj ^ (-(sigma - 1)) := by
    rw [← Real.rpow_neg_one]
    rw [← Real.rpow_add hLj]
    congr 1
    ring
  have hcast : Lj = ((2 ^ j : ℕ) : ℝ) * (L : ℝ) := by
    dsimp [Lj]
    push_cast
    ring
  have hLone : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hLpow : (L : ℝ) ^ (-(sigma - 1)) ≤ 1 := by
    calc
      (L : ℝ) ^ (-(sigma - 1)) ≤ (L : ℝ) ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hLone (by linarith)
      _ = 1 := Real.rpow_zero _
  have hpow : Lj ^ (-(sigma - 1)) ≤
      (((2 : ℝ) ^ (-(sigma - 1))) ^ j) := by
    rw [hcast, Real.mul_rpow (by positivity) (by positivity)]
    rw [two_pow_rpow_neg_eq]
    have hnonneg : 0 ≤ ((2 : ℝ) ^ (-(sigma - 1))) ^ j := by positivity
    nlinarith
  rw [hsplit]
  exact mul_le_mul_of_nonneg_left hpow (by positivity)

theorem finiteHalaszGaussianSchurShellScale_le_geometric
    {Cbeta : ℝ} {I : ℕ × ℕ} {S L j : ℕ} {sigma : ℝ}
    (hCbeta : 0 ≤ Cbeta) (hIlo : 3 ≤ I.1) (hI : I.1 ≤ I.2)
    (hL : 0 < L) (hsigma : 1 < sigma) :
    finiteHalaszGaussianSchurShellScale Cbeta I S sigma L j ≤
      (8 * finiteHalaszGaussianBetaDensity Cbeta I S ^ 2 +
        2 * (finiteHalaszGaussianBetaRemainder I S * (L : ℝ)⁻¹) ^ 2) *
        (((2 : ℝ) ^ (-2 * (sigma - 1))) ^ j) := by
  let A : ℝ := (((2 ^ (j + 1) * L : ℕ) : ℝ) *
        finiteHalaszGaussianBetaDensity Cbeta I S +
      finiteHalaszGaussianBetaRemainder I S)
  let w1 : ℝ := (((2 ^ j * L : ℕ) : ℝ)⁻¹)
  let r : ℝ := ((2 : ℝ) ^ (-(sigma - 1))) ^ j
  have hA : 0 ≤ A := by
    dsimp [A]
    exact add_nonneg
      (mul_nonneg (Nat.cast_nonneg _)
        (finiteHalaszGaussianBetaDensity_nonneg hCbeta hIlo hI))
      (by unfold finiteHalaszGaussianBetaRemainder; positivity)
  have hw := dyadic_weight_rpow_neg_le_geometric hL hsigma (j := j)
  have hmul : A * (((2 ^ j * L : ℕ) : ℝ) ^ (-sigma)) ≤
      (A * w1) * r := by
    dsimp [w1, r]
    nlinarith [mul_le_mul_of_nonneg_left hw hA]
  have hsquare :
      (A * (((2 ^ j * L : ℕ) : ℝ) ^ (-sigma))) ^ 2 ≤
        (A * w1) ^ 2 * r ^ 2 := by
    have hleft : 0 ≤ A * (((2 ^ j * L : ℕ) : ℝ) ^ (-sigma)) := by
      positivity
    calc
      _ ≤ ((A * w1) * r) ^ 2 := pow_le_pow_left₀ hleft hmul 2
      _ = (A * w1) ^ 2 * r ^ 2 := by ring
  have hone := finiteHalaszGaussianSchurShellScale_le_uniform
    hCbeta hIlo hI hL (show (1 : ℝ) ≤ 1 by norm_num)
      (S := S) (j := j) (sigma := (1 : ℝ))
  have hbase : (A * w1) ^ 2 ≤
      8 * finiteHalaszGaussianBetaDensity Cbeta I S ^ 2 +
        2 * (finiteHalaszGaussianBetaRemainder I S * (L : ℝ)⁻¹) ^ 2 := by
    simpa only [finiteHalaszGaussianSchurShellScale, A, w1,
      Real.rpow_neg_one] using hone
  have hr2 : r ^ 2 = ((2 : ℝ) ^ (-2 * (sigma - 1))) ^ j := by
    dsimp [r]
    rw [← pow_mul]
    rw [← Real.rpow_mul_natCast (show (0 : ℝ) ≤ 2 by norm_num)]
    rw [← Real.rpow_mul_natCast (show (0 : ℝ) ≤ 2 by norm_num)]
    congr 1
    push_cast
    ring
  unfold finiteHalaszGaussianSchurShellScale
  change (A * (((2 ^ j * L : ℕ) : ℝ) ^ (-sigma))) ^ 2 ≤ _
  calc
    _ ≤ (A * w1) ^ 2 * r ^ 2 := hsquare
    _ ≤ (8 * finiteHalaszGaussianBetaDensity Cbeta I S ^ 2 +
        2 * (finiteHalaszGaussianBetaRemainder I S * (L : ℝ)⁻¹) ^ 2) *
          r ^ 2 := by
      gcongr
    _ = _ := by rw [hr2]

/-- A prefix-independent bound for all Gaussian--Schur shells. -/
theorem sum_finiteHalaszGaussianSchurShellScale_le_geometric
    {Cbeta : ℝ} {I : ℕ × ℕ} {S L J : ℕ} {sigma : ℝ}
    (hCbeta : 0 ≤ Cbeta) (hIlo : 3 ≤ I.1) (hI : I.1 ≤ I.2)
    (hL : 0 < L) (hsigma : 1 < sigma) :
    (∑ j ∈ Finset.range J,
        finiteHalaszGaussianSchurShellScale Cbeta I S sigma L j) ≤
      (8 * finiteHalaszGaussianBetaDensity Cbeta I S ^ 2 +
        2 * (finiteHalaszGaussianBetaRemainder I S * (L : ℝ)⁻¹) ^ 2) *
        (1 - (2 : ℝ) ^ (-2 * (sigma - 1)))⁻¹ := by
  let q : ℝ := (2 : ℝ) ^ (-2 * (sigma - 1))
  let E : ℝ := 8 * finiteHalaszGaussianBetaDensity Cbeta I S ^ 2 +
    2 * (finiteHalaszGaussianBetaRemainder I S * (L : ℝ)⁻¹) ^ 2
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hexp : -2 * (sigma - 1) < 0 := by nlinarith
  have hq1 : q < 1 := by
    dsimp [q]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hexp
  have hE : 0 ≤ E := by dsimp [E]; positivity
  calc
    _ ≤ ∑ j ∈ Finset.range J, E * q ^ j := by
      apply Finset.sum_le_sum
      intro j _hj
      exact finiteHalaszGaussianSchurShellScale_le_geometric
        hCbeta hIlo hI hL hsigma
    _ = E * (∑ j ∈ Finset.range J, q ^ j) := by rw [Finset.mul_sum]
    _ ≤ E * (1 - q)⁻¹ := by
      gcongr
      exact sum_geometric_le_inv_one_sub hq0 hq1 J
    _ = _ := rfl

private lemma div_one_add_le_one_sub_exp_neg {x : ℝ} (hx : 0 ≤ x) :
    x / (1 + x) ≤ 1 - Real.exp (-x) := by
  have hden : 0 < 1 + x := by linarith
  have hexpmul : Real.exp (-x) * (1 + x) ≤ 1 := by
    calc
      Real.exp (-x) * (1 + x) = (1 + x) / Real.exp x := by
        rw [Real.exp_neg]
        field_simp
      _ ≤ Real.exp x / Real.exp x := by
        exact (div_le_div_iff_of_pos_right (Real.exp_pos x)).2
          (by simpa [add_comm] using Real.add_one_le_exp x)
      _ = 1 := div_self (Real.exp_ne_zero x)
  have hexp : Real.exp (-x) ≤ 1 / (1 + x) :=
    (le_div_iff₀ hden).2 (by simpa using hexpmul)
  calc
    x / (1 + x) = 1 - 1 / (1 + x) := by field_simp; ring
    _ ≤ 1 - Real.exp (-x) := sub_le_sub_left hexp 1

/-- An elementary reciprocal bound for the geometric denominator. -/
theorem inv_one_sub_two_rpow_neg_le
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    (1 - (2 : ℝ) ^ (-2 * epsilon))⁻¹ ≤
      1 + (2 * Real.log 2 * epsilon)⁻¹ := by
  let x : ℝ := 2 * Real.log 2 * epsilon
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hx : 0 < x := by dsimp [x]; positivity
  have hq : (2 : ℝ) ^ (-2 * epsilon) = Real.exp (-x) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    congr 1
    dsimp [x]
    ring
  have hlower : x / (1 + x) ≤ 1 - (2 : ℝ) ^ (-2 * epsilon) := by
    rw [hq]
    exact div_one_add_le_one_sub_exp_neg hx.le
  have hleft : 0 < x / (1 + x) := by positivity
  have hright : 0 < 1 - (2 : ℝ) ^ (-2 * epsilon) :=
    lt_of_lt_of_le hleft hlower
  have hinv := (inv_le_inv₀ hright hleft).2 hlower
  calc
    (1 - (2 : ℝ) ^ (-2 * epsilon))⁻¹ ≤ (x / (1 + x))⁻¹ := hinv
    _ = 1 + x⁻¹ := by field_simp; ring
    _ = _ := rfl

/-- At Tao's line `1 + 1 / log X`, the geometric loss is at most
`2 log X`. -/
theorem inv_one_sub_two_rpow_taoExponent_sub_one_le
    {X : ℕ} (hX : 3 ≤ X) :
    (1 - (2 : ℝ) ^
        (-2 * (Erdos67b.EulerResidue.taoExponent X - 1)))⁻¹ ≤
      2 * Real.log X := by
  have hlogX : 1 ≤ Real.log (X : ℝ) := by
    have h3X : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    have hlog3X : Real.log 3 ≤ Real.log (X : ℝ) := by
      exact Real.strictMonoOn_log.monotoneOn
        (by norm_num)
        (by
          show (0 : ℝ) < (X : ℝ)
          exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 3) hX))
        h3X
    linarith [Real.log_three_gt_d9]
  have hlogPos : 0 < Real.log (X : ℝ) := zero_lt_one.trans_le hlogX
  have hepsilon : 0 < Erdos67b.EulerResidue.taoExponent X - 1 := by
    unfold Erdos67b.EulerResidue.taoExponent
    have hi : 0 < (Real.log (X : ℝ))⁻¹ := inv_pos.mpr hlogPos
    linarith
  have hbase := inv_one_sub_two_rpow_neg_le hepsilon
  have hepsilonEq : Erdos67b.EulerResidue.taoExponent X - 1 =
      (Real.log (X : ℝ))⁻¹ := by
    unfold Erdos67b.EulerResidue.taoExponent
    ring
  have hlog2 : (1 : ℝ) ≤ 2 * Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hinv : (2 * Real.log 2 *
      (Erdos67b.EulerResidue.taoExponent X - 1))⁻¹ ≤
      Real.log (X : ℝ) := by
    rw [hepsilonEq]
    have hden : 0 < 2 * Real.log 2 := by positivity
    field_simp
    nlinarith
  calc
    _ ≤ 1 + (2 * Real.log 2 *
        (Erdos67b.EulerResidue.taoExponent X - 1))⁻¹ := hbase
    _ ≤ 1 + Real.log (X : ℝ) := by gcongr
    _ ≤ 2 * Real.log (X : ℝ) := by linarith

end Erdos67b.MRHalaszBands
