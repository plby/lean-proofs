import ErdosProblems.Erdos67b.MRGSA10PrimeLambdaDiagonal
import ErdosProblems.Erdos67b.MRGSA10PrimeLogHarmonicShell

/-!
# Beta-sensitive fixed-high prime-Lambda diagonals

The auxiliary fixed-high A.10 windows lie on the real lines `c₀ - 2β` and
`c₀`.  The old scalar diagonal bound discarded the weight `(n/N)^(4β)` on
the left line and therefore paid the full harmonic mass.  Dyadic Chebyshev
summation retains this weight and replaces that left mass by `O(1 + 1/β)`.

For the two *separate* L² diagonals this gives the paired square-root scale

`N^(2β) * sqrt (H(X) * min (H(X), C * (1 + 1/β)))`.

This is the strongest conclusion available from the *fixed-high* separate
diagonals: the unshifted right diagonal still has harmonic size `H(X)`.

The actual source windows are symmetric, on `c₀ - β` and `c₀ + β`.  For
that pair the same shell argument gives beta decay on the right as well as
beta growth on the left.  We therefore also prove the contour-facing bound

`N^β * min (H(X), C * (1 + 1/β))`

for the product of the two diagonal square roots, with `β = 0` handled by
the original harmonic budget.
-/

open scoped BigOperators

namespace Erdos67b.MRHalaszBands

noncomputable section

/-- Dyadic shell index using `n - 1`, so that the resulting shell is open
on the left and closed on the right without an endpoint exception. -/
def gsA10BetaDiagonalShellIndex (n : ℕ) : ℕ :=
  Nat.log 2 (n - 1)

theorem prime_mem_Ioc_gsA10BetaDiagonalShell (n : ℕ) (hn : n.Prime) :
    n ∈ Finset.Ioc (2 ^ gsA10BetaDiagonalShellIndex n)
      (2 ^ (gsA10BetaDiagonalShellIndex n + 1)) := by
  have hn2 : 2 ≤ n := hn.two_le
  have hnSub : n - 1 ≠ 0 := by omega
  have hlower : 2 ^ Nat.log 2 (n - 1) ≤ n - 1 :=
    Nat.pow_log_le_self 2 hnSub
  have hupper : n - 1 < 2 ^ (Nat.log 2 (n - 1)).succ :=
    Nat.lt_pow_succ_log_self (by omega) (n - 1)
  rw [Finset.mem_Ioc]
  constructor <;> simp only [gsA10BetaDiagonalShellIndex]
  · omega
  · simpa only [Nat.succ_eq_add_one] using
      (show n ≤ 2 ^ (Nat.log 2 (n - 1) + 1) by omega)

private theorem sum_range_two_rpow_delta_succ_le
    {N : ℕ} (hN : 2 ≤ N) {delta : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1) :
    (∑ j ∈ Finset.range (Nat.log 2 N + 1),
        ((2 : ℝ) ^ delta) ^ (j + 1)) ≤
      2 * (N : ℝ) ^ delta *
        (1 - (2 : ℝ) ^ (-delta))⁻¹ := by
  let M := Nat.log 2 N
  let b : ℝ := (2 : ℝ) ^ delta
  have hb1 : 1 < b := by
    dsimp only [b]
    exact Real.one_lt_rpow (by norm_num) hdelta
  have hb0 : 0 ≤ b := hb1.le.trans' zero_le_one
  have hb2 : b ≤ 2 := by
    dsimp only [b]
    calc
      (2 : ℝ) ^ delta ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hdeltaOne
      _ = 2 := by simp
  have hpowMN : b ^ M ≤ (N : ℝ) ^ delta := by
    have heq : b ^ M = ((((2 ^ M : ℕ) : ℝ)) ^ delta) := by
      dsimp only [b]
      push_cast
      rw [← Real.rpow_natCast_mul (show (0 : ℝ) ≤ 2 by norm_num)]
      rw [mul_comm]
      exact (Real.rpow_mul_natCast
        (show (0 : ℝ) ≤ 2 by norm_num) delta M).symm
    rw [heq]
    apply Real.rpow_le_rpow (by positivity)
    · exact_mod_cast Nat.pow_log_le_self 2 (by omega : N ≠ 0)
    · exact hdelta.le
  have hpowSucc : b ^ (M + 1) ≤ 2 * (N : ℝ) ^ delta := by
    rw [pow_succ]
    nlinarith [mul_le_mul hpowMN hb2 hb0
      (Real.rpow_nonneg (by positivity) delta)]
  have hden : 0 < b - 1 := sub_pos.mpr hb1
  calc
    (∑ j ∈ Finset.range (Nat.log 2 N + 1),
        ((2 : ℝ) ^ delta) ^ (j + 1)) =
        b * (∑ j ∈ Finset.range (M + 1), b ^ j) := by
      dsimp only [b, M]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [pow_succ']
    _ = b * ((b ^ (M + 1) - 1) / (b - 1)) := by
      rw [geom_sum_eq hb1.ne']
    _ ≤ b * (b ^ (M + 1) / (b - 1)) := by
      gcongr
      linarith
    _ ≤ b * ((2 * (N : ℝ) ^ delta) / (b - 1)) := by
      gcongr
    _ = 2 * (N : ℝ) ^ delta *
        (1 - (2 : ℝ) ^ (-delta))⁻¹ := by
      have hbpos : 0 < b := zero_lt_one.trans hb1
      have hq : (2 : ℝ) ^ (-delta) = b⁻¹ := by
        dsimp only [b]
        exact Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) delta
      rw [hq]
      field_simp

/-- A normalized positive beta weight turns the logarithmic prime mass of
the whole A.10 window into a convergent geometric shell sum. -/
theorem sum_vonMangoldt_div_mul_normalized_rpow_primeWindow_le
    {y X : ℕ} (hN : 2 ≤ X / y) {delta : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1) :
    (∑ n ∈ gsA10PrimeWindow y X,
        (ArithmeticFunction.vonMangoldt n / n) *
          (((n : ℝ) / (X / y : ℕ)) ^ delta)) ≤
      4 * gsA10PrimeLogHarmonicFactorFourConstant *
        (1 - (2 : ℝ) ^ (-delta))⁻¹ := by
  let N := X / y
  let D := gsA10PrimeWindow y X
  let J := Nat.log 2 N + 1
  let idx : ℕ → ℕ := gsA10BetaDiagonalShellIndex
  let term : ℕ → ℝ := fun n ↦
    (ArithmeticFunction.vonMangoldt n / n) *
      (((n : ℝ) / N) ^ delta)
  let b : ℝ := (2 : ℝ) ^ delta
  have hNpos : 0 < N := by omega
  have hNposR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hmaps : ∀ n ∈ D, idx n ∈ Finset.range J := by
    intro n hn
    have hnData := mem_gsA10PrimeWindow.mp (by simpa only [D] using hn)
    have hnN : n - 1 ≤ N := by omega
    exact Finset.mem_range.mpr (by
      dsimp only [idx, J]
      exact Nat.lt_succ_of_le (Nat.log_mono_right hnN))
  have hfiber := Finset.sum_fiberwise_of_maps_to hmaps term
  have hshell : ∀ j ∈ Finset.range J,
      (∑ n ∈ D with idx n = j, term n) ≤
        ((N : ℝ) ^ (-delta) * b ^ (j + 1)) *
          (2 * gsA10PrimeLogHarmonicFactorFourConstant) := by
    intro j hj
    have hpoint : ∀ n ∈ D.filter (fun n ↦ idx n = j),
        term n ≤
          ((N : ℝ) ^ (-delta) * b ^ (j + 1)) *
            (Real.log (n : ℝ) / n) := by
      intro n hn
      have hnD : n ∈ D := (Finset.mem_filter.mp hn).1
      have hnidx : idx n = j := (Finset.mem_filter.mp hn).2
      have hnData := mem_gsA10PrimeWindow.mp (by simpa only [D] using hnD)
      have hnposR : (0 : ℝ) < n := by exact_mod_cast hnData.2.2.pos
      have hnShell0 := prime_mem_Ioc_gsA10BetaDiagonalShell n hnData.2.2
      have hnUpper : n ≤ 2 ^ (j + 1) := by
        have := (Finset.mem_Ioc.mp hnShell0).2
        simpa only [idx, hnidx] using this
      have hratio : (n : ℝ) / N ≤
          ((2 : ℝ) ^ (j + 1)) / N := by
        exact div_le_div_of_nonneg_right
          (by exact_mod_cast hnUpper) hNposR.le
      have hpow := Real.rpow_le_rpow
        (div_nonneg (by positivity) hNposR.le) hratio hdelta.le
      have hfactor :
          (((2 : ℝ) ^ (j + 1)) / N) ^ delta =
            (N : ℝ) ^ (-delta) * b ^ (j + 1) := by
        rw [Real.div_rpow (by positivity) hNposR.le]
        have hnum : (((2 : ℝ) ^ (j + 1)) ^ delta) =
            ((2 : ℝ) ^ delta) ^ (j + 1) := by
          rw [← Real.rpow_natCast_mul (show (0 : ℝ) ≤ 2 by norm_num)]
          rw [mul_comm]
          exact Real.rpow_mul_natCast
            (show (0 : ℝ) ≤ 2 by norm_num) delta (j + 1)
        rw [hnum, Real.rpow_neg hNposR.le delta]
        dsimp only [b]
        ring
      have hlog0 : 0 ≤ Real.log (n : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hnData.2.2.one_le)
      dsimp only [term]
      rw [ArithmeticFunction.vonMangoldt_apply_prime hnData.2.2]
      calc
        (Real.log (n : ℝ) / n) *
            (((n : ℝ) / N) ^ delta) ≤
            (Real.log (n : ℝ) / n) *
              (((2 : ℝ) ^ (j + 1) / N) ^ delta) :=
          mul_le_mul_of_nonneg_left hpow (div_nonneg hlog0 (by positivity))
        _ = _ := by rw [hfactor]; ring
    calc
      (∑ n ∈ D with idx n = j, term n) ≤
          ∑ n ∈ D.filter (fun n ↦ idx n = j),
            ((N : ℝ) ^ (-delta) * b ^ (j + 1)) *
              (Real.log (n : ℝ) / n) :=
        Finset.sum_le_sum hpoint
      _ = ((N : ℝ) ^ (-delta) * b ^ (j + 1)) *
          ∑ n ∈ D.filter (fun n ↦ idx n = j),
            Real.log (n : ℝ) / n := by rw [Finset.mul_sum]
      _ ≤ ((N : ℝ) ^ (-delta) * b ^ (j + 1)) *
          (2 * gsA10PrimeLogHarmonicFactorFourConstant) := by
        apply mul_le_mul_of_nonneg_left
        · let F := D.filter fun n ↦ idx n = j
          have hsubset : F ⊆ gsA10PrimeWindow y X := by
            intro n hn
            have := (Finset.mem_filter.mp hn).1
            simpa only [F, D] using this
          have hshell : ∀ n ∈ F, 2 ^ j < n ∧ n ≤ 2 ^ (j + 1) := by
            intro n hn
            have hnFilter := Finset.mem_filter.mp hn
            have hnData := mem_gsA10PrimeWindow.mp (hsubset hn)
            have hnShell0 := prime_mem_Ioc_gsA10BetaDiagonalShell n hnData.2.2
            simpa only [F, idx, hnFilter.2] using Finset.mem_Ioc.mp hnShell0
          have hinterval : F ⊆
              PrimeEstimates.primesInInterval (2 ^ j) (2 ^ (j + 1)) := by
            intro n hn
            have hnData := mem_gsA10PrimeWindow.mp (hsubset hn)
            exact PrimeEstimates.mem_primesInInterval.mpr
              ⟨(hshell n hn).1, (hshell n hn).2, hnData.2.2⟩
          have hraw :=
            sum_primeLog_div_subset_interval_le_factorFourConstant
              (S := F)
              (show 0 < 2 ^ j by positivity)
              (Nat.pow_le_pow_right (by omega) (by omega : j ≤ j + 1))
              (show 2 ^ (j + 1) ≤ 4 * 2 ^ j by
                rw [pow_succ]
                omega)
              hinterval
          have hC0 : 0 ≤ gsA10PrimeLogHarmonicFactorFourConstant :=
            gsA10PrimeLogHarmonicFactorFourConstant_nonneg
          have hraw' := hraw.trans (show
            gsA10PrimeLogHarmonicFactorFourConstant ≤
              2 * gsA10PrimeLogHarmonicFactorFourConstant by linarith)
          simpa only [F] using hraw'
        · positivity
  calc
    (∑ n ∈ gsA10PrimeWindow y X,
        (ArithmeticFunction.vonMangoldt n / n) *
          (((n : ℝ) / (X / y : ℕ)) ^ delta)) =
        ∑ j ∈ Finset.range J, ∑ n ∈ D with idx n = j, term n := by
      simpa only [D, N, term] using hfiber.symm
    _ ≤ ∑ j ∈ Finset.range J,
        ((N : ℝ) ^ (-delta) * b ^ (j + 1)) *
          (2 * gsA10PrimeLogHarmonicFactorFourConstant) :=
      Finset.sum_le_sum hshell
    _ = (2 * gsA10PrimeLogHarmonicFactorFourConstant) * (N : ℝ) ^ (-delta) *
        ∑ j ∈ Finset.range J, b ^ (j + 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ ≤ (2 * gsA10PrimeLogHarmonicFactorFourConstant) * (N : ℝ) ^ (-delta) *
        (2 * (N : ℝ) ^ delta *
          (1 - (2 : ℝ) ^ (-delta))⁻¹) := by
      apply mul_le_mul_of_nonneg_left
      · simpa only [N, J, b] using
          sum_range_two_rpow_delta_succ_le hN hdelta hdeltaOne
      · exact mul_nonneg
          (mul_nonneg (by norm_num)
            gsA10PrimeLogHarmonicFactorFourConstant_nonneg)
          (Real.rpow_nonneg (by positivity) _)
    _ = 4 * gsA10PrimeLogHarmonicFactorFourConstant *
        (1 - (2 : ℝ) ^ (-delta))⁻¹ := by
      rw [Real.rpow_neg hNposR.le delta]
      have hpowne : (N : ℝ) ^ delta ≠ 0 :=
        (Real.rpow_pos_of_pos hNposR delta).ne'
      field_simp [hpowne]
      ring

/-- Explicit positive-beta version of the preceding geometric bound. -/
theorem sum_vonMangoldt_div_mul_normalized_rpow_primeWindow_le_beta
    {y X : ℕ} (hN : 2 ≤ X / y) {beta : ℝ}
    (hbeta : 0 < beta) (hbetaQuarter : beta ≤ 1 / 4) :
    (∑ n ∈ gsA10PrimeWindow y X,
        (ArithmeticFunction.vonMangoldt n / n) *
          (((n : ℝ) / (X / y : ℕ)) ^ (4 * beta))) ≤
      4 * gsA10PrimeLogHarmonicFactorFourConstant *
        (1 + (4 * Real.log 2 * beta)⁻¹) := by
  have hraw := sum_vonMangoldt_div_mul_normalized_rpow_primeWindow_le
    hN (show 0 < 4 * beta by positivity) (show 4 * beta ≤ 1 by linarith)
  have hgeom := inv_one_sub_two_rpow_neg_le
    (show 0 < (4 * beta) / 2 by positivity)
  have hrewrite :
      -2 * ((4 * beta) / 2) = -(4 * beta) := by ring
  rw [hrewrite] at hgeom
  have hcoef : 2 * Real.log 2 * ((4 * beta) / 2) =
      4 * Real.log 2 * beta := by ring
  rw [hcoef] at hgeom
  calc
    _ ≤ 4 * gsA10PrimeLogHarmonicFactorFourConstant *
        (1 - (2 : ℝ) ^ (-(4 * beta)))⁻¹ := hraw
    _ ≤ 4 * gsA10PrimeLogHarmonicFactorFourConstant *
        (1 + (4 * Real.log 2 * beta)⁻¹) := by
      apply mul_le_mul_of_nonneg_left
      · exact hgeom
      · exact mul_nonneg (by norm_num)
          gsA10PrimeLogHarmonicFactorFourConstant_nonneg

private theorem sum_range_geometric_le_inv_one_sub_betaDiagonal
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (J : ℕ) :
    (∑ j ∈ Finset.range J, q ^ j) ≤ (1 - q)⁻¹ := by
  have hs := summable_geometric_of_lt_one hq0 hq1
  exact
    (hs.sum_le_tsum (Finset.range J)
      (fun j _hj ↦ pow_nonneg hq0 j)).trans_eq
        (tsum_geometric_of_lt_one hq0 hq1)

/-- The decaying beta weight on the right source line also has geometric
prime mass.  Unlike the left line, no top-of-window power is extracted. -/
theorem sum_vonMangoldt_div_mul_rpow_neg_primeWindow_le
    (y X : ℕ) {delta : ℝ} (hdelta : 0 < delta) :
    (∑ n ∈ gsA10PrimeWindow y X,
        (ArithmeticFunction.vonMangoldt n / n) *
          (n : ℝ) ^ (-delta)) ≤
      gsA10PrimeLogHarmonicFactorFourConstant *
        (1 - (2 : ℝ) ^ (-delta))⁻¹ := by
  let D := gsA10PrimeWindow y X
  let idx : ℕ → ℕ := gsA10BetaDiagonalShellIndex
  let term : ℕ → ℝ := fun n ↦
    (ArithmeticFunction.vonMangoldt n / n) * (n : ℝ) ^ (-delta)
  let q : ℝ := (2 : ℝ) ^ (-delta)
  have hq0 : 0 ≤ q := by dsimp only [q]; positivity
  have hq1 : q < 1 := by
    dsimp only [q]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hmaps : ∀ n ∈ D, idx n ∈ Finset.range X := by
    intro n hn
    have hnData := mem_gsA10PrimeWindow.mp (by simpa only [D] using hn)
    rw [Finset.mem_range]
    dsimp only [idx, gsA10BetaDiagonalShellIndex]
    have hidx : Nat.log 2 (n - 1) ≤ n - 1 := Nat.log_le_self 2 (n - 1)
    have hnX : n < X := hnData.2.1.trans_le (Nat.div_le_self X y)
    omega
  have hfiber := Finset.sum_fiberwise_of_maps_to hmaps term
  have hshell : ∀ j ∈ Finset.range X,
      (∑ n ∈ D with idx n = j, term n) ≤
        q ^ j * gsA10PrimeLogHarmonicFactorFourConstant := by
    intro j hj
    let F := D.filter fun n ↦ idx n = j
    have hsubset : F ⊆ gsA10PrimeWindow y X := by
      intro n hn
      have := (Finset.mem_filter.mp hn).1
      simpa only [F, D] using this
    have hshellBounds : ∀ n ∈ F, 2 ^ j < n ∧ n ≤ 2 ^ (j + 1) := by
      intro n hn
      have hnFilter := Finset.mem_filter.mp hn
      have hnData := mem_gsA10PrimeWindow.mp (hsubset hn)
      have hnShell0 := prime_mem_Ioc_gsA10BetaDiagonalShell n hnData.2.2
      simpa only [F, idx, hnFilter.2] using Finset.mem_Ioc.mp hnShell0
    have hinterval : F ⊆
        PrimeEstimates.primesInInterval (2 ^ j) (2 ^ (j + 1)) := by
      intro n hn
      have hnData := mem_gsA10PrimeWindow.mp (hsubset hn)
      exact PrimeEstimates.mem_primesInInterval.mpr
        ⟨(hshellBounds n hn).1, (hshellBounds n hn).2, hnData.2.2⟩
    have hmass := sum_primeLog_div_subset_interval_le_factorFourConstant
      (S := F)
      (show 0 < 2 ^ j by positivity)
      (Nat.pow_le_pow_right (by omega) (by omega : j ≤ j + 1))
      (show 2 ^ (j + 1) ≤ 4 * 2 ^ j by rw [pow_succ]; omega)
      hinterval
    have hpoint : ∀ n ∈ F,
        term n ≤ q ^ j * (Real.log (n : ℝ) / n) := by
      intro n hn
      have hnData := mem_gsA10PrimeWindow.mp (hsubset hn)
      have hnLower := (hshellBounds n hn).1
      have hpow : (n : ℝ) ^ (-delta) ≤ ((2 : ℝ) ^ j) ^ (-delta) := by
        exact Real.rpow_le_rpow_of_nonpos (by positivity)
          (by exact_mod_cast hnLower.le) (by linarith)
      have heq : (((2 : ℝ) ^ j) ^ (-delta)) = q ^ j := by
        dsimp only [q]
        rw [← Real.rpow_natCast_mul (show (0 : ℝ) ≤ 2 by norm_num)]
        rw [mul_comm]
        exact (Real.rpow_mul_natCast
          (show (0 : ℝ) ≤ 2 by norm_num) (-delta) j)
      have hlog0 : 0 ≤ Real.log (n : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hnData.2.2.one_le)
      dsimp only [term]
      rw [ArithmeticFunction.vonMangoldt_apply_prime hnData.2.2]
      calc
        (Real.log (n : ℝ) / n) * (n : ℝ) ^ (-delta) ≤
            (Real.log (n : ℝ) / n) * (((2 : ℝ) ^ j) ^ (-delta)) :=
          mul_le_mul_of_nonneg_left hpow (div_nonneg hlog0 (by positivity))
        _ = _ := by rw [heq]; ring
    calc
      (∑ n ∈ D with idx n = j, term n) ≤
          ∑ n ∈ F, q ^ j * (Real.log (n : ℝ) / n) :=
        Finset.sum_le_sum hpoint
      _ = q ^ j * ∑ n ∈ F, Real.log (n : ℝ) / n := by
        rw [Finset.mul_sum]
      _ ≤ q ^ j * gsA10PrimeLogHarmonicFactorFourConstant :=
        mul_le_mul_of_nonneg_left (by simpa only [F] using hmass)
          (pow_nonneg hq0 j)
  calc
    (∑ n ∈ gsA10PrimeWindow y X,
        (ArithmeticFunction.vonMangoldt n / n) *
          (n : ℝ) ^ (-delta)) =
        ∑ j ∈ Finset.range X, ∑ n ∈ D with idx n = j, term n := by
      simpa only [D, term] using hfiber.symm
    _ ≤ ∑ j ∈ Finset.range X,
        q ^ j * gsA10PrimeLogHarmonicFactorFourConstant :=
      Finset.sum_le_sum hshell
    _ = gsA10PrimeLogHarmonicFactorFourConstant *
        ∑ j ∈ Finset.range X, q ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ ≤ gsA10PrimeLogHarmonicFactorFourConstant * (1 - q)⁻¹ := by
      apply mul_le_mul_of_nonneg_left
      · exact sum_range_geometric_le_inv_one_sub_betaDiagonal hq0 hq1 X
      · exact gsA10PrimeLogHarmonicFactorFourConstant_nonneg
    _ = _ := rfl

/-- Explicit source-beta form of the decaying right-line mass. -/
theorem sum_vonMangoldt_div_mul_rpow_neg_primeWindow_le_beta
    (y X : ℕ) {beta : ℝ} (hbeta : 0 < beta) :
    (∑ n ∈ gsA10PrimeWindow y X,
        (ArithmeticFunction.vonMangoldt n / n) *
          (n : ℝ) ^ (-2 * beta)) ≤
      gsA10PrimeLogHarmonicFactorFourConstant *
        (1 + (2 * Real.log 2 * beta)⁻¹) := by
  have hraw := sum_vonMangoldt_div_mul_rpow_neg_primeWindow_le
    y X (show 0 < 2 * beta by positivity)
  have hraw' :
      (∑ n ∈ gsA10PrimeWindow y X,
          (ArithmeticFunction.vonMangoldt n / n) *
            (n : ℝ) ^ (-2 * beta)) ≤
        gsA10PrimeLogHarmonicFactorFourConstant *
          (1 - (2 : ℝ) ^ (-2 * beta))⁻¹ := by
    simpa only [show -(2 * beta) = -2 * beta by ring] using hraw
  have hgeom := inv_one_sub_two_rpow_neg_le hbeta
  calc
    _ ≤ gsA10PrimeLogHarmonicFactorFourConstant *
        (1 - (2 : ℝ) ^ (-2 * beta))⁻¹ := hraw'
    _ ≤ gsA10PrimeLogHarmonicFactorFourConstant *
        (1 + (2 * Real.log 2 * beta)⁻¹) := by
      exact mul_le_mul_of_nonneg_left hgeom
        gsA10PrimeLogHarmonicFactorFourConstant_nonneg

/-- The beta-sensitive harmonic budget, with the endpoint `beta = 0`
defined to be the original logarithmic budget. -/
def gsA10PrimeLambdaBetaDiagonalBudget (X : ℕ) (beta : ℝ) : ℝ :=
  if beta = 0 then gsA10PrimeLambdaHarmonicBudget X
  else min (gsA10PrimeLambdaHarmonicBudget X)
    (4 * gsA10PrimeLogHarmonicFactorFourConstant *
      (1 + (4 * Real.log 2 * beta)⁻¹))

theorem gsA10PrimeLambdaBetaDiagonalBudget_nonneg
    {X : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta) :
    0 ≤ gsA10PrimeLambdaBetaDiagonalBudget X beta := by
  unfold gsA10PrimeLambdaBetaDiagonalBudget
  split_ifs with hzero
  · unfold gsA10PrimeLambdaHarmonicBudget
    positivity
  · apply le_min
    · unfold gsA10PrimeLambdaHarmonicBudget
      positivity
    · have hbetapos : 0 < beta := lt_of_le_of_ne hbeta (Ne.symm hzero)
      have : 0 < 4 * Real.log 2 * beta := by positivity
      exact mul_nonneg
        (mul_nonneg (by norm_num)
          gsA10PrimeLogHarmonicFactorFourConstant_nonneg)
        (by positivity)

/-- Sharp separate-diagonal bound for the fixed-high left line
`c₀ - 2β`. -/
theorem sum_gsA10PrimeLambdaSchurWeight_fixedHigh_left_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y X : ℕ} (hX : 2 ≤ X) (hN : 2 ≤ X / y)
    {beta : ℝ} (hbeta : 0 ≤ beta) (hbetaQuarter : beta ≤ 1 / 4) :
    (∑ n ∈ gsA10PrimeWindow y X,
        gsA10PrimeLambdaSchurWeight hmul y
          (Erdos67b.EulerResidue.taoExponent X - 2 * beta) n) ≤
      ((X / y : ℕ) : ℝ) ^ (4 * beta) *
        gsA10PrimeLambdaBetaDiagonalBudget X beta := by
  by_cases hzero : beta = 0
  · subst beta
    simpa [gsA10PrimeLambdaBetaDiagonalBudget] using
      (sum_gsA10PrimeLambdaSchurWeight_tao_sub_le
        hmul hbound hX (show (0 : ℝ) ≤ 0 by norm_num))
  have hbetapos : 0 < beta := lt_of_le_of_ne hbeta (Ne.symm hzero)
  have hharm := sum_gsA10PrimeLambdaSchurWeight_tao_sub_le
    (y := y) hmul hbound hX (show 0 ≤ 2 * beta by positivity)
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hpoint : ∀ n ∈ gsA10PrimeWindow y X,
      gsA10PrimeLambdaSchurWeight hmul y
          (Erdos67b.EulerResidue.taoExponent X - 2 * beta) n ≤
        ((X / y : ℕ) : ℝ) ^ (4 * beta) *
          ((ArithmeticFunction.vonMangoldt n / n) *
            (((n : ℝ) / (X / y : ℕ)) ^ (4 * beta))) := by
    intro n hn
    have hnData := mem_gsA10PrimeWindow.mp hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hnData.2.2.pos
    have hNpos : (0 : ℝ) < ((X / y : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < X / y by omega)
    have hpowTao :
        (n : ℝ) ^
            (1 - 2 * (Erdos67b.EulerResidue.taoExponent X - 2 * beta)) ≤
          (n : ℝ) ^ (-1 + 4 * beta) := by
      apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hnData.2.2.one_le)
      unfold Erdos67b.EulerResidue.taoExponent
      have : 0 < (Real.log (X : ℝ))⁻¹ := inv_pos.mpr hlogX
      linarith
    calc
      gsA10PrimeLambdaSchurWeight hmul y
          (Erdos67b.EulerResidue.taoExponent X - 2 * beta) n ≤
          ArithmeticFunction.vonMangoldt n *
            (n : ℝ) ^
              (1 - 2 * (Erdos67b.EulerResidue.taoExponent X - 2 * beta)) :=
        gsA10PrimeLambdaSchurWeight_le_vonMangoldt hmul hbound hn
      _ ≤ ArithmeticFunction.vonMangoldt n *
          (n : ℝ) ^ (-1 + 4 * beta) :=
        mul_le_mul_of_nonneg_left hpowTao ArithmeticFunction.vonMangoldt_nonneg
      _ = ((X / y : ℕ) : ℝ) ^ (4 * beta) *
          ((ArithmeticFunction.vonMangoldt n / n) *
            (((n : ℝ) / (X / y : ℕ)) ^ (4 * beta))) := by
        rw [Real.rpow_add hnpos, Real.rpow_neg_one]
        rw [Real.div_rpow hnpos.le hNpos.le]
        have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
        have hNpowne : (((X / y : ℕ) : ℝ) ^ (4 * beta)) ≠ 0 :=
          (Real.rpow_pos_of_pos hNpos _).ne'
        field_simp [hnne, hNpowne]
  have hbetaBound :=
    sum_vonMangoldt_div_mul_normalized_rpow_primeWindow_le_beta
      hN hbetapos hbetaQuarter
  have hsharp :
      (∑ n ∈ gsA10PrimeWindow y X,
          gsA10PrimeLambdaSchurWeight hmul y
            (Erdos67b.EulerResidue.taoExponent X - 2 * beta) n) ≤
        ((X / y : ℕ) : ℝ) ^ (4 * beta) *
          (4 * gsA10PrimeLogHarmonicFactorFourConstant *
            (1 + (4 * Real.log 2 * beta)⁻¹)) := by
    calc
      _ ≤ ∑ n ∈ gsA10PrimeWindow y X,
          ((X / y : ℕ) : ℝ) ^ (4 * beta) *
            ((ArithmeticFunction.vonMangoldt n / n) *
              (((n : ℝ) / (X / y : ℕ)) ^ (4 * beta))) :=
        Finset.sum_le_sum hpoint
      _ = ((X / y : ℕ) : ℝ) ^ (4 * beta) *
          ∑ n ∈ gsA10PrimeWindow y X,
            ((ArithmeticFunction.vonMangoldt n / n) *
              (((n : ℝ) / (X / y : ℕ)) ^ (4 * beta))) := by
        rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hbetaBound (by positivity)
  rw [gsA10PrimeLambdaBetaDiagonalBudget, if_neg hzero]
  rw [mul_min_of_nonneg _ _ (Real.rpow_nonneg (by positivity) _)]
  apply le_min
  · simpa only [show 2 * (2 * beta) = 4 * beta by ring] using hharm
  · exact hsharp

/-- The fixed-high right diagonal is the beta-zero Tao-line diagonal. -/
theorem sum_gsA10PrimeLambdaSchurWeight_fixedHigh_right_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y X : ℕ} (hX : 2 ≤ X) :
    (∑ n ∈ gsA10PrimeWindow y X,
        gsA10PrimeLambdaSchurWeight hmul y
          (Erdos67b.EulerResidue.taoExponent X) n) ≤
      gsA10PrimeLambdaHarmonicBudget X := by
  simpa using sum_gsA10PrimeLambdaSchurWeight_tao_add_le
    hmul hbound hX (show (0 : ℝ) ≤ 0 by norm_num)

/-- Product form of the two beta-sensitive fixed-high diagonals. -/
theorem mul_sum_gsA10PrimeLambdaSchurWeight_fixedHigh_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y X : ℕ} (hX : 2 ≤ X) (hN : 2 ≤ X / y)
    {beta : ℝ} (hbeta : 0 ≤ beta) (hbetaQuarter : beta ≤ 1 / 4) :
    (∑ n ∈ gsA10PrimeWindow y X,
        gsA10PrimeLambdaSchurWeight hmul y
          (Erdos67b.EulerResidue.taoExponent X - 2 * beta) n) *
      (∑ n ∈ gsA10PrimeWindow y X,
        gsA10PrimeLambdaSchurWeight hmul y
          (Erdos67b.EulerResidue.taoExponent X) n) ≤
      ((X / y : ℕ) : ℝ) ^ (4 * beta) *
        (gsA10PrimeLambdaBetaDiagonalBudget X beta *
          gsA10PrimeLambdaHarmonicBudget X) := by
  have hleft := sum_gsA10PrimeLambdaSchurWeight_fixedHigh_left_le
    hmul hbound hX hN hbeta hbetaQuarter
  have hright := sum_gsA10PrimeLambdaSchurWeight_fixedHigh_right_le
    (y := y) hmul hbound hX
  have hleft0 : 0 ≤
      ∑ n ∈ gsA10PrimeWindow y X,
        gsA10PrimeLambdaSchurWeight hmul y
          (Erdos67b.EulerResidue.taoExponent X - 2 * beta) n := by
    apply Finset.sum_nonneg
    intro n hn
    unfold gsA10PrimeLambdaSchurWeight
    positivity
  have hright0 : 0 ≤
      ∑ n ∈ gsA10PrimeWindow y X,
        gsA10PrimeLambdaSchurWeight hmul y
          (Erdos67b.EulerResidue.taoExponent X) n := by
    apply Finset.sum_nonneg
    intro n hn
    unfold gsA10PrimeLambdaSchurWeight
    positivity
  calc
    _ ≤ (((X / y : ℕ) : ℝ) ^ (4 * beta) *
          gsA10PrimeLambdaBetaDiagonalBudget X beta) *
        gsA10PrimeLambdaHarmonicBudget X :=
      mul_le_mul hleft hright hright0
        (mul_nonneg (Real.rpow_nonneg (by positivity) _)
          (gsA10PrimeLambdaBetaDiagonalBudget_nonneg hbeta))
    _ = _ := by ring

/-- Beta-sensitive diagonal budget for the actual symmetric source lines
`c₀ - beta` and `c₀ + beta`. -/
def gsA10PrimeLambdaSymmetricBetaDiagonalBudget
    (X : ℕ) (beta : ℝ) : ℝ :=
  if beta = 0 then gsA10PrimeLambdaHarmonicBudget X
  else min (gsA10PrimeLambdaHarmonicBudget X)
    (4 * gsA10PrimeLogHarmonicFactorFourConstant *
      (1 + (2 * Real.log 2 * beta)⁻¹))

theorem gsA10PrimeLambdaSymmetricBetaDiagonalBudget_nonneg
    {X : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta) :
    0 ≤ gsA10PrimeLambdaSymmetricBetaDiagonalBudget X beta := by
  unfold gsA10PrimeLambdaSymmetricBetaDiagonalBudget
  split_ifs with hzero
  · unfold gsA10PrimeLambdaHarmonicBudget
    positivity
  · apply le_min
    · unfold gsA10PrimeLambdaHarmonicBudget
      positivity
    · have hbetapos : 0 < beta := lt_of_le_of_ne hbeta (Ne.symm hzero)
      have hden : 0 < 2 * Real.log 2 * beta := by positivity
      exact mul_nonneg
        (mul_nonneg (by norm_num)
          gsA10PrimeLogHarmonicFactorFourConstant_nonneg)
        (by positivity)

private theorem
    sum_vonMangoldt_div_mul_normalized_rpow_primeWindow_le_symmetricBeta
    {y X : ℕ} (hN : 2 ≤ X / y) {beta : ℝ}
    (hbeta : 0 < beta) (hbetaHalf : beta ≤ 1 / 2) :
    (∑ n ∈ gsA10PrimeWindow y X,
        (ArithmeticFunction.vonMangoldt n / n) *
          (((n : ℝ) / (X / y : ℕ)) ^ (2 * beta))) ≤
      4 * gsA10PrimeLogHarmonicFactorFourConstant *
        (1 + (2 * Real.log 2 * beta)⁻¹) := by
  have hraw := sum_vonMangoldt_div_mul_normalized_rpow_primeWindow_le
    hN (show 0 < 2 * beta by positivity) (show 2 * beta ≤ 1 by linarith)
  have hgeom := inv_one_sub_two_rpow_neg_le hbeta
  calc
    _ ≤ 4 * gsA10PrimeLogHarmonicFactorFourConstant *
        (1 - (2 : ℝ) ^ (-2 * beta))⁻¹ := by
      simpa only [show -(2 * beta) = -2 * beta by ring] using hraw
    _ ≤ 4 * gsA10PrimeLogHarmonicFactorFourConstant *
        (1 + (2 * Real.log 2 * beta)⁻¹) :=
      mul_le_mul_of_nonneg_left hgeom
        (mul_nonneg (by norm_num)
          gsA10PrimeLogHarmonicFactorFourConstant_nonneg)

/-- Left diagonal on the actual source line `c₀ - beta`. -/
theorem sum_gsA10PrimeLambdaSchurWeight_symmetric_left_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y X : ℕ} (hX : 2 ≤ X) (hN : 2 ≤ X / y)
    {beta : ℝ} (hbeta : 0 ≤ beta) (hbetaHalf : beta ≤ 1 / 2) :
    (∑ n ∈ gsA10PrimeWindow y X,
        gsA10PrimeLambdaSchurWeight hmul y
          (Erdos67b.EulerResidue.taoExponent X - beta) n) ≤
      ((X / y : ℕ) : ℝ) ^ (2 * beta) *
        gsA10PrimeLambdaSymmetricBetaDiagonalBudget X beta := by
  by_cases hzero : beta = 0
  · subst beta
    simpa [gsA10PrimeLambdaSymmetricBetaDiagonalBudget] using
      (sum_gsA10PrimeLambdaSchurWeight_tao_sub_le
        (y := y) hmul hbound hX (show (0 : ℝ) ≤ 0 by norm_num))
  have hbetapos : 0 < beta := lt_of_le_of_ne hbeta (Ne.symm hzero)
  have hharm := sum_gsA10PrimeLambdaSchurWeight_tao_sub_le
    (y := y) hmul hbound hX hbeta
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hpoint : ∀ n ∈ gsA10PrimeWindow y X,
      gsA10PrimeLambdaSchurWeight hmul y
          (Erdos67b.EulerResidue.taoExponent X - beta) n ≤
        ((X / y : ℕ) : ℝ) ^ (2 * beta) *
          ((ArithmeticFunction.vonMangoldt n / n) *
            (((n : ℝ) / (X / y : ℕ)) ^ (2 * beta))) := by
    intro n hn
    have hnData := mem_gsA10PrimeWindow.mp hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hnData.2.2.pos
    have hNpos : (0 : ℝ) < ((X / y : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < X / y by omega)
    have hpowTao :
        (n : ℝ) ^
            (1 - 2 * (Erdos67b.EulerResidue.taoExponent X - beta)) ≤
          (n : ℝ) ^ (-1 + 2 * beta) := by
      apply Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast hnData.2.2.one_le)
      unfold Erdos67b.EulerResidue.taoExponent
      have : 0 < (Real.log (X : ℝ))⁻¹ := inv_pos.mpr hlogX
      linarith
    calc
      gsA10PrimeLambdaSchurWeight hmul y
          (Erdos67b.EulerResidue.taoExponent X - beta) n ≤
          ArithmeticFunction.vonMangoldt n *
            (n : ℝ) ^
              (1 - 2 * (Erdos67b.EulerResidue.taoExponent X - beta)) :=
        gsA10PrimeLambdaSchurWeight_le_vonMangoldt hmul hbound hn
      _ ≤ ArithmeticFunction.vonMangoldt n *
          (n : ℝ) ^ (-1 + 2 * beta) :=
        mul_le_mul_of_nonneg_left hpowTao ArithmeticFunction.vonMangoldt_nonneg
      _ = ((X / y : ℕ) : ℝ) ^ (2 * beta) *
          ((ArithmeticFunction.vonMangoldt n / n) *
            (((n : ℝ) / (X / y : ℕ)) ^ (2 * beta))) := by
        rw [Real.rpow_add hnpos, Real.rpow_neg_one]
        rw [Real.div_rpow hnpos.le hNpos.le]
        have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
        have hNpowne : (((X / y : ℕ) : ℝ) ^ (2 * beta)) ≠ 0 :=
          (Real.rpow_pos_of_pos hNpos _).ne'
        field_simp [hnne, hNpowne]
  have hbetaBound :=
    sum_vonMangoldt_div_mul_normalized_rpow_primeWindow_le_symmetricBeta
      hN hbetapos hbetaHalf
  have hsharp :
      (∑ n ∈ gsA10PrimeWindow y X,
          gsA10PrimeLambdaSchurWeight hmul y
            (Erdos67b.EulerResidue.taoExponent X - beta) n) ≤
        ((X / y : ℕ) : ℝ) ^ (2 * beta) *
          (4 * gsA10PrimeLogHarmonicFactorFourConstant *
            (1 + (2 * Real.log 2 * beta)⁻¹)) := by
    calc
      _ ≤ ∑ n ∈ gsA10PrimeWindow y X,
          ((X / y : ℕ) : ℝ) ^ (2 * beta) *
            ((ArithmeticFunction.vonMangoldt n / n) *
              (((n : ℝ) / (X / y : ℕ)) ^ (2 * beta))) :=
        Finset.sum_le_sum hpoint
      _ = ((X / y : ℕ) : ℝ) ^ (2 * beta) *
          ∑ n ∈ gsA10PrimeWindow y X,
            ((ArithmeticFunction.vonMangoldt n / n) *
              (((n : ℝ) / (X / y : ℕ)) ^ (2 * beta))) := by
        rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hbetaBound (by positivity)
  rw [gsA10PrimeLambdaSymmetricBetaDiagonalBudget, if_neg hzero]
  rw [mul_min_of_nonneg _ _ (Real.rpow_nonneg (by positivity) _)]
  exact le_min hharm hsharp

/-- Right diagonal on the actual source line `c₀ + beta`. -/
theorem sum_gsA10PrimeLambdaSchurWeight_symmetric_right_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y X : ℕ} (hX : 2 ≤ X)
    {beta : ℝ} (hbeta : 0 ≤ beta) :
    (∑ n ∈ gsA10PrimeWindow y X,
        gsA10PrimeLambdaSchurWeight hmul y
          (Erdos67b.EulerResidue.taoExponent X + beta) n) ≤
      gsA10PrimeLambdaSymmetricBetaDiagonalBudget X beta := by
  by_cases hzero : beta = 0
  · subst beta
    simpa [gsA10PrimeLambdaSymmetricBetaDiagonalBudget] using
      (sum_gsA10PrimeLambdaSchurWeight_tao_add_le
        (y := y) hmul hbound hX (show (0 : ℝ) ≤ 0 by norm_num))
  have hbetapos : 0 < beta := lt_of_le_of_ne hbeta (Ne.symm hzero)
  have hharm := sum_gsA10PrimeLambdaSchurWeight_tao_add_le
    (y := y) hmul hbound hX hbeta
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hpoint : ∀ n ∈ gsA10PrimeWindow y X,
      gsA10PrimeLambdaSchurWeight hmul y
          (Erdos67b.EulerResidue.taoExponent X + beta) n ≤
        (ArithmeticFunction.vonMangoldt n / n) *
          (n : ℝ) ^ (-2 * beta) := by
    intro n hn
    have hnData := mem_gsA10PrimeWindow.mp hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hnData.2.2.pos
    have hpowTao :
        (n : ℝ) ^
            (1 - 2 * (Erdos67b.EulerResidue.taoExponent X + beta)) ≤
          (n : ℝ) ^ (-1 - 2 * beta) := by
      apply Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast hnData.2.2.one_le)
      unfold Erdos67b.EulerResidue.taoExponent
      have : 0 < (Real.log (X : ℝ))⁻¹ := inv_pos.mpr hlogX
      linarith
    calc
      gsA10PrimeLambdaSchurWeight hmul y
          (Erdos67b.EulerResidue.taoExponent X + beta) n ≤
          ArithmeticFunction.vonMangoldt n *
            (n : ℝ) ^
              (1 - 2 * (Erdos67b.EulerResidue.taoExponent X + beta)) :=
        gsA10PrimeLambdaSchurWeight_le_vonMangoldt hmul hbound hn
      _ ≤ ArithmeticFunction.vonMangoldt n *
          (n : ℝ) ^ (-1 - 2 * beta) :=
        mul_le_mul_of_nonneg_left hpowTao ArithmeticFunction.vonMangoldt_nonneg
      _ = (ArithmeticFunction.vonMangoldt n / n) *
          (n : ℝ) ^ (-2 * beta) := by
        rw [show -1 - 2 * beta = (-1 : ℝ) + (-2 * beta) by ring]
        rw [Real.rpow_add hnpos, Real.rpow_neg_one]
        field_simp
  have hsharp :
      (∑ n ∈ gsA10PrimeWindow y X,
          gsA10PrimeLambdaSchurWeight hmul y
            (Erdos67b.EulerResidue.taoExponent X + beta) n) ≤
        4 * gsA10PrimeLogHarmonicFactorFourConstant *
          (1 + (2 * Real.log 2 * beta)⁻¹) := by
    calc
      _ ≤ ∑ n ∈ gsA10PrimeWindow y X,
          (ArithmeticFunction.vonMangoldt n / n) *
            (n : ℝ) ^ (-2 * beta) := Finset.sum_le_sum hpoint
      _ ≤ gsA10PrimeLogHarmonicFactorFourConstant *
          (1 + (2 * Real.log 2 * beta)⁻¹) :=
        sum_vonMangoldt_div_mul_rpow_neg_primeWindow_le_beta y X hbetapos
      _ ≤ 4 * gsA10PrimeLogHarmonicFactorFourConstant *
          (1 + (2 * Real.log 2 * beta)⁻¹) := by
        have hfactor : 0 ≤ 1 + (2 * Real.log 2 * beta)⁻¹ := by positivity
        nlinarith [gsA10PrimeLogHarmonicFactorFourConstant_nonneg]
  rw [gsA10PrimeLambdaSymmetricBetaDiagonalBudget, if_neg hzero]
  exact le_min hharm hsharp

/-- Source-sharp product of the two symmetric prime-Lambda diagonals. -/
theorem mul_sum_gsA10PrimeLambdaSchurWeight_symmetric_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y X : ℕ} (hX : 2 ≤ X) (hN : 2 ≤ X / y)
    {beta : ℝ} (hbeta : 0 ≤ beta) (hbetaHalf : beta ≤ 1 / 2) :
    (∑ n ∈ gsA10PrimeWindow y X,
        gsA10PrimeLambdaSchurWeight hmul y
          (Erdos67b.EulerResidue.taoExponent X - beta) n) *
      (∑ n ∈ gsA10PrimeWindow y X,
        gsA10PrimeLambdaSchurWeight hmul y
          (Erdos67b.EulerResidue.taoExponent X + beta) n) ≤
      ((X / y : ℕ) : ℝ) ^ (2 * beta) *
        (gsA10PrimeLambdaSymmetricBetaDiagonalBudget X beta) ^ 2 := by
  have hleft := sum_gsA10PrimeLambdaSchurWeight_symmetric_left_le
    hmul hbound hX hN hbeta hbetaHalf
  have hright := sum_gsA10PrimeLambdaSchurWeight_symmetric_right_le
    (y := y) hmul hbound hX hbeta
  have hleft0 : 0 ≤
      ∑ n ∈ gsA10PrimeWindow y X,
        gsA10PrimeLambdaSchurWeight hmul y
          (Erdos67b.EulerResidue.taoExponent X - beta) n := by
    apply Finset.sum_nonneg
    intro n hn
    unfold gsA10PrimeLambdaSchurWeight
    positivity
  have hright0 : 0 ≤
      ∑ n ∈ gsA10PrimeWindow y X,
        gsA10PrimeLambdaSchurWeight hmul y
          (Erdos67b.EulerResidue.taoExponent X + beta) n := by
    apply Finset.sum_nonneg
    intro n hn
    unfold gsA10PrimeLambdaSchurWeight
    positivity
  have hB0 := gsA10PrimeLambdaSymmetricBetaDiagonalBudget_nonneg
    (X := X) hbeta
  calc
    _ ≤ (((X / y : ℕ) : ℝ) ^ (2 * beta) *
          gsA10PrimeLambdaSymmetricBetaDiagonalBudget X beta) *
        gsA10PrimeLambdaSymmetricBetaDiagonalBudget X beta :=
      mul_le_mul hleft hright hright0
        (mul_nonneg (Real.rpow_nonneg (by positivity) _) hB0)
    _ = _ := by ring

/-- Contour-facing square-root form of the symmetric diagonal estimate.
This is the source scale `(X/y)^beta * min(log X, C * (1 + 1/beta))`,
with the endpoint `beta = 0` interpreted by the harmonic budget. -/
theorem rpow_half_sum_gsA10PrimeLambdaSchurWeight_symmetric_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y X : ℕ} (hX : 2 ≤ X) (hN : 2 ≤ X / y)
    {beta : ℝ} (hbeta : 0 ≤ beta) (hbetaHalf : beta ≤ 1 / 2) :
    (∑ n ∈ gsA10PrimeWindow y X,
        gsA10PrimeLambdaSchurWeight hmul y
          (Erdos67b.EulerResidue.taoExponent X - beta) n) ^
          ((1 : ℝ) / 2) *
      (∑ n ∈ gsA10PrimeWindow y X,
        gsA10PrimeLambdaSchurWeight hmul y
          (Erdos67b.EulerResidue.taoExponent X + beta) n) ^
          ((1 : ℝ) / 2) ≤
      ((X / y : ℕ) : ℝ) ^ beta *
        gsA10PrimeLambdaSymmetricBetaDiagonalBudget X beta := by
  let L : ℝ := ∑ n ∈ gsA10PrimeWindow y X,
    gsA10PrimeLambdaSchurWeight hmul y
      (Erdos67b.EulerResidue.taoExponent X - beta) n
  let R : ℝ := ∑ n ∈ gsA10PrimeWindow y X,
    gsA10PrimeLambdaSchurWeight hmul y
      (Erdos67b.EulerResidue.taoExponent X + beta) n
  let q : ℝ := ((X / y : ℕ) : ℝ)
  let B : ℝ := gsA10PrimeLambdaSymmetricBetaDiagonalBudget X beta
  have hL0 : 0 ≤ L := by
    dsimp only [L]
    apply Finset.sum_nonneg
    intro n hn
    unfold gsA10PrimeLambdaSchurWeight
    positivity
  have hR0 : 0 ≤ R := by
    dsimp only [R]
    apply Finset.sum_nonneg
    intro n hn
    unfold gsA10PrimeLambdaSchurWeight
    positivity
  have hq0 : 0 ≤ q := by dsimp only [q]; positivity
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    exact gsA10PrimeLambdaSymmetricBetaDiagonalBudget_nonneg
      (X := X) hbeta
  have hleft := sum_gsA10PrimeLambdaSchurWeight_symmetric_left_le
    hmul hbound hX hN hbeta hbetaHalf
  have hright := sum_gsA10PrimeLambdaSchurWeight_symmetric_right_le
    (y := y) hmul hbound hX hbeta
  have hLhalf : L ^ ((1 : ℝ) / 2) ≤
      q ^ beta * B ^ ((1 : ℝ) / 2) := by
    calc
      L ^ ((1 : ℝ) / 2) ≤
          (q ^ (2 * beta) * B) ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow hL0 (by simpa only [L, q, B] using hleft)
          (by norm_num)
      _ = (q ^ (2 * beta)) ^ ((1 : ℝ) / 2) *
          B ^ ((1 : ℝ) / 2) := by
        rw [Real.mul_rpow (Real.rpow_nonneg hq0 _) hB0]
      _ = q ^ beta * B ^ ((1 : ℝ) / 2) := by
        rw [← Real.rpow_mul hq0]
        congr 2
        ring
  have hRhalf : R ^ ((1 : ℝ) / 2) ≤ B ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow hR0 (by simpa only [R, B] using hright) (by norm_num)
  calc
    L ^ ((1 : ℝ) / 2) * R ^ ((1 : ℝ) / 2) ≤
        (q ^ beta * B ^ ((1 : ℝ) / 2)) * B ^ ((1 : ℝ) / 2) :=
      mul_le_mul hLhalf hRhalf (Real.rpow_nonneg hR0 _)
        (mul_nonneg (Real.rpow_nonneg hq0 _) (Real.rpow_nonneg hB0 _))
    _ = q ^ beta *
        (B ^ ((1 : ℝ) / 2) * B ^ ((1 : ℝ) / 2)) := by ring
    _ = q ^ beta * B := by
      rw [← Real.sqrt_eq_rpow, Real.mul_self_sqrt hB0]
    _ = _ := rfl

end

end Erdos67b.MRHalaszBands

#print axioms Erdos67b.MRHalaszBands.sum_vonMangoldt_div_mul_normalized_rpow_primeWindow_le_beta
#print axioms Erdos67b.MRHalaszBands.sum_gsA10PrimeLambdaSchurWeight_fixedHigh_left_le
#print axioms Erdos67b.MRHalaszBands.mul_sum_gsA10PrimeLambdaSchurWeight_fixedHigh_le
#print axioms Erdos67b.MRHalaszBands.mul_sum_gsA10PrimeLambdaSchurWeight_symmetric_le
#print axioms Erdos67b.MRHalaszBands.rpow_half_sum_gsA10PrimeLambdaSchurWeight_symmetric_le
