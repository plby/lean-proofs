/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos285.Proposition7
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The terminal mass estimate in Martin's Proposition 7

The correction has two parts.  The large-prime-power stages have total mass
`o(1 / log y)` by the square-tail estimate in `RoughCounts`.  At a small
prime-power stage `q = p^e`, the initial least common multiple acquires exactly
the factor `p`.  Thus the costs `(p-1)/lcm(1,...,q)` telescope and their total
is strictly less than one.

This file also packages the numerical facts for Martin's choice
`lo = floor(log y)`.  The exported theorem has no hypothesis supplying a mass
bound: that bound is obtained here from the two proved estimates above.
-/

namespace Erdos285.Proposition7Mass

open Filter Finset Real
open scoped BigOperators Topology

noncomputable section

open PrimePowers RoughCounts

/-! ## The exact small-prime-power telescope -/

/-- At a prime power, division by the newly acquired prime factor recovers the
preceding initial LCM.  This is the pointwise identity behind the ordered
prime-power telescope. -/
theorem initialLcm_div_minFac_eq_pred {q : ℕ} (hq : IsPrimePow q) :
    initialLcm q / q.minFac = initialLcm (q - 1) := by
  obtain ⟨p, e, hp, he, rfl⟩ := (isPrimePow_nat_iff _).mp hq
  rw [LcmTelescope.initialLcm_prime_pow hp he.ne', hp.pow_minFac he.ne']
  exact Nat.mul_div_right _ hp.pos

/-- The sum of the small-stage costs is the exact endpoint difference. -/
theorem small_prime_power_mass_telescope (lo : ℕ) :
    (∑ q ∈ primePowersUpTo lo,
        ((q.minFac - 1 : ℕ) : ℚ) / initialLcm q) =
      1 - (1 : ℚ) / initialLcm lo := by
  change LcmTelescope.smallPrimePowerCost lo =
    1 - (1 : ℚ) / initialLcm lo
  exact LcmTelescope.smallPrimePowerCost_eq lo

/-- In particular, all small-prime-power correction terms cost less than one. -/
theorem small_prime_power_mass_lt_one (lo : ℕ) :
    (∑ q ∈ primePowersUpTo lo,
        ((q.minFac - 1 : ℕ) : ℚ) / initialLcm q) < 1 := by
  change LcmTelescope.smallPrimePowerCost lo < 1
  exact LcmTelescope.smallPrimePowerCost_lt_one lo

/-! ## Numerical facts at `lo = floor(log y)` -/

private lemma log_four_lt_two : Real.log 4 < 2 := by
  rw [Real.log_four_eq]
  have hlog2 : Real.log 2 < 1 :=
    (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)).2
      Real.exp_one_gt_two
  linarith

/-- The explicit Chebyshev estimate gives `psi(n) ≤ 2n` eventually. -/
theorem eventually_psi_nat_le_two_mul :
    ∀ᶠ n : ℕ in atTop, Chebyshev.psi (n : ℝ) ≤ 2 * n := by
  let ε : ℝ := (2 - Real.log 4) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith [log_four_lt_two]
  have hsmall :=
    (isLittleO_log_rpow_atTop (r := (1 : ℝ) / 2) (by norm_num)).bound hε
  filter_upwards
    [eventually_ge_atTop 1,
      tendsto_natCast_atTop_atTop.eventually hsmall]
      with n hn hlog
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsqrt : Real.sqrt (n : ℝ) ^ 2 = n := by
    rw [sq_sqrt]
    positivity
  have hlognonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
  have hsqrtnonneg : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hrpow : (n : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt n := by
    exact (Real.sqrt_eq_rpow (n : ℝ)).symm
  have hnormLog : ‖Real.log (n : ℝ)‖ = Real.log n :=
    Real.norm_of_nonneg hlognonneg
  have hnormSqrt : ‖(n : ℝ) ^ ((1 : ℝ) / 2)‖ = Real.sqrt n := by
    rw [hrpow, Real.norm_of_nonneg hsqrtnonneg]
  rw [hnormLog, hnormSqrt] at hlog
  have herror :
      2 * Real.sqrt (n : ℝ) * Real.log n ≤
        (2 - Real.log 4) * n := by
    calc
      2 * Real.sqrt (n : ℝ) * Real.log n ≤
          2 * Real.sqrt (n : ℝ) *
            (((2 - Real.log 4) / 2) * Real.sqrt n) :=
        mul_le_mul_of_nonneg_left (by simpa [ε] using hlog)
          (mul_nonneg (by norm_num) hsqrtnonneg)
      _ = (2 - Real.log 4) * (Real.sqrt n) ^ 2 := by ring
      _ = (2 - Real.log 4) * n := by rw [hsqrt]
  calc
    Chebyshev.psi (n : ℝ) ≤
        Real.log 4 * n + 2 * Real.sqrt n * Real.log n :=
      Chebyshev.psi_le hnR
    _ ≤ 2 * n := by linarith

/-- Consequently `lcm(1,...,n) ≤ exp(2n)` eventually. -/
theorem eventually_initialLcm_le_exp_two_mul :
    ∀ᶠ n : ℕ in atTop,
      (initialLcm n : ℝ) ≤ Real.exp (2 * n) := by
  filter_upwards [eventually_psi_nat_le_two_mul] with n hn
  have hpos : (0 : ℝ) < initialLcm n := by
    exact_mod_cast (Nat.lcmUpto_pos n)
  have hlog : Real.log (initialLcm n : ℝ) ≤ 2 * n := by
    change Real.log (Nat.lcmUpto n : ℝ) ≤ 2 * (n : ℝ)
    rw [← Chebyshev.psi_eq_log_lcmUpto]
    exact hn
  have := Real.exp_monotone hlog
  simpa [Real.exp_log hpos] using this

/-- At the logarithmic cutoff, the LCM needed by Lemma 16 is eventually at
most `y²`. -/
theorem eventually_initialLcm_naturalLogCutoff_le_sq :
    ∀ᶠ y : ℕ in atTop,
      initialLcm (naturalLogCutoff y) ≤ y ^ 2 := by
  have hLcm := eventually_psi_nat_le_two_mul.filter_mono
    naturalLogCutoff_tendsto_atTop
  filter_upwards
    [hLcm,
      eventually_ge_atTop 2,
      tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))]
      with y hLcm hy hlog
  have hypos : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
  have hfloor : (naturalLogCutoff y : ℝ) ≤ Real.log (y : ℝ) := by
    exact Nat.floor_le hlog.le
  exact Proposition7.initialLcm_le_sq_of_chebyshev (by omega) hfloor hLcm

lemma eventually_naturalLogCutoff_le_self :
    ∀ᶠ y : ℕ in atTop, naturalLogCutoff y ≤ y := by
  filter_upwards
    [eventually_ge_atTop 1,
      tendsto_log_coe_at_top.eventually (eventually_ge_atTop (0 : ℝ))]
      with y hy hlog
  have hfloor : (naturalLogCutoff y : ℝ) ≤ Real.log (y : ℝ) :=
    Nat.floor_le hlog
  have hypos : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
  have hlogLe : Real.log (y : ℝ) ≤ y := by
    linarith [Real.log_le_sub_one_of_pos hypos]
  exact_mod_cast hfloor.trans hlogLe

lemma eventually_naturalLogCutoff_lt_half :
    ∀ᶠ y : ℕ in atTop, naturalLogCutoff y < y / 2 := by
  filter_upwards [eventually_ge_atTop 40] with y hy
  have hlog := Proposition7.log_lt_quarter_natCast y hy
  have hlognonneg : 0 ≤ Real.log (y : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ y by omega))
  have hfloor : (naturalLogCutoff y : ℝ) ≤ Real.log (y : ℝ) :=
    Nat.floor_le hlognonneg
  have hfourR : (4 * naturalLogCutoff y : ℕ) < (y : ℝ) := by
    push_cast
    nlinarith
  have hfour : 4 * naturalLogCutoff y < y := by exact_mod_cast hfourR
  omega

/-! ## Eventual mass and exact correction -/

/-- The complete preliminary correction has reciprocal mass below
`1 + c/log y`, with no assumed mass estimate. -/
theorem eventually_exists_budgeted_preliminary
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ y : ℕ in atTop, ∀ r : ℚ,
      largestPrimePowerPart r.den ≤ y →
      ∃ E : Finset ℕ,
        Proposition7.BudgetedPreliminaryResult
          (naturalLogCutoff y) y r E ∧
        (UnitFractions.rec_sum E : ℝ) <
          1 + c / Real.log (y : ℝ) := by
  filter_upwards
    [naturalLogCutoff_tendsto_atTop.eventually (eventually_ge_atTop 3),
      eventually_naturalLogCutoff_le_self,
      eventually_initialLcm_naturalLogCutoff_le_sq,
      RoughCounts.eventually_sum_ten_div_primePower_sq_lt_div_log hc]
      with y hlo hloy hL htail
  intro r hry
  obtain ⟨E, hE⟩ :=
    Proposition7.exists_budgetedPreliminaryResult_of_lemmas
      (naturalLogCutoff y) y hlo hloy hL r hry
  refine ⟨E, hE, ?_⟩
  calc
    (UnitFractions.rec_sum E : ℝ) <
        1 + Proposition7.largeSquareCost (naturalLogCutoff y) y :=
      hE.rec_sum_lt
    _ ≤ 1 + c / Real.log (y : ℝ) := by
      simp only [Proposition7.largeSquareCost]
      linarith

/-- If the input residual is larger than the large-stage error and is below
one, the integer left by the preliminary correction lies in `(-1,1)`. -/
theorem terminal_residual_abs_lt_one
    {c : ℝ} {y : ℕ} {r : ℚ} {E : Finset ℕ}
    (hrLower : c / Real.log (y : ℝ) < (r : ℝ))
    (hrUpper : (r : ℝ) < 1)
    (hmass : (UnitFractions.rec_sum E : ℝ) <
      1 + c / Real.log (y : ℝ)) :
    |r - UnitFractions.rec_sum E| < (1 : ℚ) := by
  have hsumQ : 0 ≤ UnitFractions.rec_sum E := UnitFractions.rec_sum_nonneg
  have hsum : (0 : ℝ) ≤ UnitFractions.rec_sum E := by exact_mod_cast hsumQ
  have hlower : (-1 : ℝ) <
      (r : ℝ) - UnitFractions.rec_sum E := by linarith
  have hupper : (r : ℝ) - UnitFractions.rec_sum E < 1 := by linarith
  have habs : |(r : ℝ) - UnitFractions.rec_sum E| < 1 :=
    (abs_lt).2 ⟨hlower, hupper⟩
  exact_mod_cast habs

/-- Eventual, source-faithful Proposition 7.  It instantiates the cutoff,
proves the LCM and mass bounds internally, and returns exactly `2*piStar y`
distinct unit fractions. -/
theorem eventually_proposition7
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ y : ℕ in atTop, ∀ r : ℚ,
      largestPrimePowerPart r.den ≤ y →
      c / Real.log (y : ℝ) < (r : ℝ) →
      (r : ℝ) < 1 →
      ∃ E : Finset ℕ,
        E.card = 2 * piStar y ∧
        UnitFractions.rec_sum E = r ∧
        0 ∉ E ∧
        ∀ n ∈ E, n ≤ 2 * y ^ 4 := by
  filter_upwards
    [eventually_ge_atTop 40,
      naturalLogCutoff_tendsto_atTop.eventually (eventually_ge_atTop 3),
      eventually_naturalLogCutoff_le_self,
      eventually_naturalLogCutoff_lt_half,
      eventually_initialLcm_naturalLogCutoff_le_sq,
      RoughCounts.eventually_sum_ten_div_primePower_sq_lt_div_log hc]
      with y hy hlo hloy hlohalf hL htail
  intro r hry hrLower hrUpper
  exact Proposition7.proposition7_of_cutoff hc hy hlo hloy hlohalf hL hry
    hrLower hrUpper htail

end

end Erdos285.Proposition7Mass
