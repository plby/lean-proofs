/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AppendixA11A12ScaleCertificate
import ErdosProblems.Erdos1165.AppendixPairMoment
import ErdosProblems.Erdos1165.TerminalNegativeBinomialWindow

/-!
# Numerical reserve for the annular one-point transfer

The walk-facing part of HLOZ Appendix A loses fixed initial/final factors,
the terminal negative-binomial window, and a product of small annular row
errors.  This file records a deliberately generous polynomial reserve inside
the exponential `annularHistoryLoss`.  Keeping this estimate explicit makes
the final literal event comparison insensitive to harmless constant choices.
-/

open Filter
open scoped Topology

namespace Erdos1165.AnnularHistoryLossNumerical

open AppendixA11A12ScaleCertificate Proposition13Scales AppendixPairMoment
  AppendixFirstMoment TerminalNegativeBinomialWindow

noncomputable section

/-- The annular history reserve is eventually smaller than the reciprocal
of the same degree-24 polynomial already used in the pair estimate. -/
theorem eventually_annularHistoryLoss_le_inv_pairPolynomial
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop,
      annularHistoryLoss delta n ≤
        1 / (256 * (scaleIndex delta n + 1 : ℕ) ^ (24 : ℕ) : ℝ) := by
  filter_upwards [eventually_pairPolynomial_le_exp_quarter_cost hdelta]
      with n hpoly
  let q : ℝ := scaleIndex delta n
  let A : ℝ := 256 * (scaleIndex delta n + 1 : ℕ) ^ (24 : ℕ)
  have hApos : 0 < A := by
    dsimp [A]
    positivity
  have hcost : 0 ≤ scaleCost delta n := by
    unfold scaleCost
    positivity
  have hmul : A * annularHistoryLoss delta n ≤ 1 := by
    calc
      A * annularHistoryLoss delta n ≤
          Real.exp (scaleCost delta n / 4) *
            Real.exp (-(1 / 2 : ℝ) * scaleCost delta n) := by
              exact mul_le_mul_of_nonneg_right hpoly
                (annularHistoryLoss_pos delta n).le
      _ = Real.exp (-(1 / 4 : ℝ) * scaleCost delta n) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ 1 := by
        have hneg : -(1 / 4 : ℝ) * scaleCost delta n ≤ 0 := by
          exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) hcost
        simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hneg
  change annularHistoryLoss delta n ≤ 1 / A
  exact (le_div_iff₀ hApos).2 (by simpa [mul_comm] using hmul)

/-- Even after reserving a factor `1/2³⁰` for the forced initial crossing,
the initial and final spatial pieces, and the internal row comparison, the
elementary terminal-window mass still dominates `annularHistoryLoss`. -/
theorem eventually_annularHistoryLoss_le_one_div_two_pow_thirty_mul_terminalWindow
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ N : ℕ in atTop,
      ∀ (hq2 : 2 ≤ scaleIndex delta N)
        (m : Profile (scaleIndex delta N)),
        IsConstrainedProfile chosenProfileDelta m →
          annularHistoryLoss delta N ≤
            (1 / 1073741824 : ℝ) *
              terminalWindowMass (scaleIndex delta N) chosenProfileDelta
                (terminalProfileCount hq2 m) := by
  have hscaleNat : Tendsto (scaleIndex delta) atTop atTop :=
    tendsto_natCast_atTop_iff.mp (tendsto_scaleIndex_atTop delta)
  have hlogTop : Tendsto
      (fun q : ℕ ↦ 3 * Real.log (q : ℝ)) atTop atTop := by
    exact Filter.Tendsto.const_mul_atTop (by norm_num)
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [eventually_annularHistoryLoss_le_inv_pairPolynomial hdelta,
      hscaleNat.eventually (eventually_ge_atTop 15),
      hscaleNat.eventually (hlogTop.eventually (eventually_ge_atTop 1))]
      with N hhistory hq15 hlog
  intro hq2 m hm
  let q : ℕ := scaleIndex delta N
  let count : ℕ := terminalProfileCount hq2 m
  let terminalCeil : ℕ :=
    ⌈2 * ((count : ℝ) / (3 * Real.log q))⌉₊
  have hterminal :=
    one_div_thirtyTwo_ceil_two_terminalProfileMean_le_terminalWindowMass_of_bounds
      (by omega) (by norm_num [chosenProfileDelta]) hm hlog
  have hcountBounds := terminalProfileCount_bounds hq2
    (by norm_num [chosenProfileDelta]) hm
  have hdenPos : 0 < 3 * Real.log (q : ℝ) :=
    lt_of_lt_of_le zero_lt_one hlog
  have hratioUpper : (count : ℝ) / (3 * Real.log q) ≤ count :=
    div_le_self (by positivity) hlog
  have hceil : terminalCeil ≤ 6 * q ^ 2 := by
    rw [show terminalCeil =
      ⌈2 * ((count : ℝ) / (3 * Real.log q))⌉₊ from rfl, Nat.ceil_le]
    calc
      2 * ((count : ℝ) / (3 * Real.log q)) ≤ 2 * count := by gcongr
      _ ≤ 6 * (q : ℝ) ^ 2 := by
        dsimp only [count]
        nlinarith [hcountBounds.2]
      _ = ((6 * q ^ 2 : ℕ) : ℝ) := by norm_num
  have hcountPos : 0 < (count : ℝ) := by
    dsimp only [count]
    have hqPos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    nlinarith [hcountBounds.1]
  have hterminalCeilPos : 0 < terminalCeil := by
    apply Nat.ceil_pos.mpr
    exact mul_pos (by norm_num) (div_pos hcountPos hdenPos)
  have hpower : (805306368 : ℝ) * (q : ℝ) ^ 2 ≤
      ((q : ℝ) + 1) ^ (24 : ℕ) := by
    have hqOne : (1 : ℝ) ≤ (q : ℝ) + 1 := by
      have hq0 : (0 : ℝ) ≤ q := by positivity
      linarith
    have hconst : (805306368 : ℝ) ≤
        ((q : ℝ) + 1) ^ (8 : ℕ) := by
      calc
        (805306368 : ℝ) ≤ 16 ^ (8 : ℕ) := by norm_num
        _ ≤ ((q : ℝ) + 1) ^ (8 : ℕ) := by
          gcongr
          exact_mod_cast (show 16 ≤ q + 1 by omega)
    have hqSq : (q : ℝ) ^ (2 : ℕ) ≤
        ((q : ℝ) + 1) ^ (16 : ℕ) := by
      calc
        (q : ℝ) ^ (2 : ℕ) ≤ ((q : ℝ) + 1) ^ (2 : ℕ) := by
          gcongr
          exact_mod_cast (show q ≤ q + 1 by omega)
        _ ≤ ((q : ℝ) + 1) ^ (16 : ℕ) :=
          pow_le_pow_right₀ hqOne (by norm_num)
    calc
      (805306368 : ℝ) * (q : ℝ) ^ 2 ≤
          ((q : ℝ) + 1) ^ 8 * ((q : ℝ) + 1) ^ 16 :=
        mul_le_mul hconst hqSq (by positivity) (by positivity)
      _ = ((q : ℝ) + 1) ^ 24 := by ring
  let smallDenominator : ℝ := 1073741824 * (32 * terminalCeil)
  let largeDenominator : ℝ :=
    256 * (scaleIndex delta N + 1 : ℕ) ^ (24 : ℕ)
  have hsmallPos : 0 < smallDenominator := by
    dsimp [smallDenominator]
    positivity
  have hdenominator : smallDenominator ≤ largeDenominator := by
    dsimp only [smallDenominator, largeDenominator]
    norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_pow,
      Nat.cast_mul, Nat.cast_ofNat]
    calc
      1073741824 * (32 * (terminalCeil : ℝ)) ≤
          1073741824 * (32 * (6 * (q : ℝ) ^ 2)) := by
            gcongr
            exact_mod_cast hceil
      _ = 256 * ((805306368 : ℝ) * (q : ℝ) ^ 2) := by ring
      _ ≤ 256 * ((q : ℝ) + 1) ^ 24 := by gcongr
      _ = 256 * (↑(scaleIndex delta N) + 1) ^ 24 := by rfl
  have hinv : 1 / largeDenominator ≤ 1 / smallDenominator :=
    one_div_le_one_div_of_le hsmallPos hdenominator
  calc
    annularHistoryLoss delta N ≤ 1 / largeDenominator := by
      simpa only [largeDenominator] using hhistory
    _ ≤ (1 / 1073741824 : ℝ) * (1 / (32 * terminalCeil)) := by
      calc
        1 / largeDenominator ≤ 1 / smallDenominator := hinv
        _ = (1 / 1073741824 : ℝ) * (1 / (32 * terminalCeil)) := by
          dsimp [smallDenominator]
          field_simp
    _ ≤ (1 / 1073741824 : ℝ) *
        terminalWindowMass q chosenProfileDelta count := by
      gcongr

end

end Erdos1165.AnnularHistoryLossNumerical
