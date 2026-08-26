import ErdosProblems.Erdos67b.MRGSA9A13ShiftedFinite

/-!
# Source-shaped horizontal displacement for A.13

The low line in the A.10 rectangle may lie just to the left of `Re s = 1`.
The elementary displacement estimate below therefore retains the actual
left-line weight instead of replacing it prematurely by `1 / p`.
-/

open scoped BigOperators
open Complex

namespace Erdos67b.MRHalaszBands

noncomputable section

open BoundedGaps.Maynard

/-- Exact radial factorization of a prime monomial between two vertical
lines having the same imaginary part. -/
theorem nat_cpow_neg_low_eq_rpow_gap_mul_neg_high
    {p : ℕ} (hp : p.Prime) {sigmaLow sigmaHigh t : ℝ}
    (_hle : sigmaLow ≤ sigmaHigh) :
    (p : ℂ) ^ (-((sigmaLow : ℂ) + Complex.I * (t : ℂ))) =
      (((p : ℝ) ^ (sigmaHigh - sigmaLow) : ℝ) : ℂ) *
        (p : ℂ) ^ (-((sigmaHigh : ℂ) + Complex.I * (t : ℂ))) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hrealPow : ((((p : ℝ) ^ (sigmaHigh - sigmaLow) : ℝ) : ℂ)) =
      (p : ℂ) ^ ((sigmaHigh - sigmaLow : ℝ) : ℂ) :=
    Complex.ofReal_cpow hpR.le (sigmaHigh - sigmaLow)
  rw [hrealPow, ← Complex.cpow_add _ _ hpC]
  congr 1
  push_cast
  ring

/-- The radial norm displacement is the gap times `log p`, weighted on the
left line.  This remains valid even when the left line is slightly below
one. -/
theorem norm_nat_cpow_neg_low_sub_high_le_gap_mul_log_mul_low
    {p : ℕ} (hp : p.Prime) {sigmaLow sigmaHigh t : ℝ}
    (hle : sigmaLow ≤ sigmaHigh) :
    ‖(p : ℂ) ^ (-((sigmaLow : ℂ) + Complex.I * (t : ℂ)))‖ -
        ‖(p : ℂ) ^ (-((sigmaHigh : ℂ) + Complex.I * (t : ℂ)))‖ ≤
      (sigmaHigh - sigmaLow) * Real.log p *
        ‖(p : ℂ) ^ (-((sigmaLow : ℂ) + Complex.I * (t : ℂ)))‖ := by
  let d : ℝ := sigmaHigh - sigmaLow
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hd : 0 ≤ d := sub_nonneg.mpr hle
  have hlogp : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hx : 0 ≤ d * Real.log p := mul_nonneg hd hlogp
  have hone : 1 - Real.exp (-(d * Real.log p)) ≤ d * Real.log p := by
    linarith [Real.one_sub_le_exp_neg (d * Real.log p)]
  rw [Erdos67b.HalaszCpowDeficit.norm_nat_cpow_neg_sigma_add_I_mul hp.pos,
    Erdos67b.HalaszCpowDeficit.norm_nat_cpow_neg_sigma_add_I_mul hp.pos,
    Real.rpow_def_of_pos hpR, Real.rpow_def_of_pos hpR]
  rw [show Real.log (p : ℝ) * -sigmaLow = -sigmaLow * Real.log p by ring,
    show Real.log (p : ℝ) * -sigmaHigh = -sigmaHigh * Real.log p by ring]
  have hhigh : Real.exp (-sigmaHigh * Real.log p) =
      Real.exp (-sigmaLow * Real.log p) * Real.exp (-(d * Real.log p)) := by
    rw [← Real.exp_add]
    congr 1
    dsimp only [d]
    ring
  rw [hhigh]
  calc
    Real.exp (-sigmaLow * Real.log p) -
          Real.exp (-sigmaLow * Real.log p) * Real.exp (-(d * Real.log p)) =
        Real.exp (-sigmaLow * Real.log p) *
          (1 - Real.exp (-(d * Real.log p))) := by ring
    _ ≤ Real.exp (-sigmaLow * Real.log p) * (d * Real.log p) := by
      gcongr
    _ = (sigmaHigh - sigmaLow) * Real.log p *
        Real.exp (-sigmaLow * Real.log p) := by
      dsimp only [d]
      ring

/-- Summed radial displacement under a pointwise `K / p` majorant on the
left line. -/
theorem sum_prime_radial_norm_sub_le_mul_primeLogHarmonicSum
    {y : ℕ} {sigmaLow sigmaHigh t K : ℝ}
    (hle : sigmaLow ≤ sigmaHigh)
    (hweight : ∀ p ∈ primesUpTo y,
      ‖(p : ℂ) ^ (-((sigmaLow : ℂ) + Complex.I * (t : ℂ)))‖ ≤
        K / (p : ℝ)) :
    (∑ p ∈ primesUpTo y,
      (‖(p : ℂ) ^ (-((sigmaLow : ℂ) + Complex.I * (t : ℂ)))‖ -
        ‖(p : ℂ) ^ (-((sigmaHigh : ℂ) + Complex.I * (t : ℂ)))‖)) ≤
      K * (sigmaHigh - sigmaLow) * primeLogHarmonicSum y := by
  have hgap : 0 ≤ sigmaHigh - sigmaLow := sub_nonneg.mpr hle
  calc
    (∑ p ∈ primesUpTo y,
      (‖(p : ℂ) ^ (-((sigmaLow : ℂ) + Complex.I * (t : ℂ)))‖ -
        ‖(p : ℂ) ^ (-((sigmaHigh : ℂ) + Complex.I * (t : ℂ)))‖)) ≤
        ∑ p ∈ primesUpTo y,
          ((sigmaHigh - sigmaLow) * Real.log p *
            ‖(p : ℂ) ^ (-((sigmaLow : ℂ) + Complex.I * (t : ℂ)))‖) := by
      apply Finset.sum_le_sum
      intro p hp
      exact norm_nat_cpow_neg_low_sub_high_le_gap_mul_log_mul_low
        (mem_primesUpTo.mp hp).1 hle
    _ ≤ ∑ p ∈ primesUpTo y,
          ((sigmaHigh - sigmaLow) * Real.log p * (K / (p : ℝ))) := by
      apply Finset.sum_le_sum
      intro p hp
      have hlogp : 0 ≤ Real.log (p : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (mem_primesUpTo.mp hp).1.one_le)
      exact mul_le_mul_of_nonneg_left (hweight p hp)
        (mul_nonneg hgap hlogp)
    _ = ∑ p ∈ primesUpTo y,
          ((K * (sigmaHigh - sigmaLow)) * (Real.log p / (p : ℝ))) := by
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ = K * (sigmaHigh - sigmaLow) * primeLogHarmonicSum y := by
      rw [← Finset.mul_sum]
      unfold primeLogHarmonicSum primesUpTo
      rw [Nat.primesLE_eq_filter_range]

/-- On the source A.10 left line, which is at worst `2 / log y` to the
left of one, every prime monomial through `y` is bounded by `e² / p`. -/
theorem norm_prime_cpow_sourceLow_le_exp_two_div
    {p y : ℕ} (hp : p.Prime) (hpy : p ≤ y) {sigmaLow t : ℝ}
    (hsigma : 1 - 2 / Real.log (y : ℝ) ≤ sigmaLow) :
    ‖(p : ℂ) ^ (-((sigmaLow : ℂ) + Complex.I * (t : ℂ)))‖ ≤
      Real.exp 2 / (p : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hyOne : (1 : ℝ) < y := by
    exact_mod_cast hp.one_lt.trans_le hpy
  have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos hyOne
  have hlogp : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hlogle : Real.log (p : ℝ) ≤ Real.log (y : ℝ) := by
    exact Real.log_le_log hpR (by exact_mod_cast hpy)
  have hratio : Real.log (p : ℝ) / Real.log (y : ℝ) ≤ 1 :=
    (div_le_one hlogy).mpr hlogle
  have htwo : 2 / Real.log (y : ℝ) * Real.log (p : ℝ) ≤ 2 := by
    calc
      2 / Real.log (y : ℝ) * Real.log (p : ℝ) =
          2 * (Real.log (p : ℝ) / Real.log (y : ℝ)) := by ring
      _ ≤ 2 * 1 := by gcongr
      _ = 2 := by ring
  have hmul := mul_le_mul_of_nonneg_right hsigma hlogp
  have hexponent : Real.log (p : ℝ) * -sigmaLow ≤
      2 - Real.log (p : ℝ) := by
    have haux : Real.log (p : ℝ) - 2 ≤
        (1 - 2 / Real.log (y : ℝ)) * Real.log (p : ℝ) := by
      rw [sub_mul, one_mul]
      linarith
    nlinarith
  rw [Erdos67b.HalaszCpowDeficit.norm_nat_cpow_neg_sigma_add_I_mul hp.pos,
    Real.rpow_def_of_pos hpR]
  calc
    Real.exp (Real.log (p : ℝ) * -sigmaLow) ≤
        Real.exp (2 - Real.log (p : ℝ)) := Real.exp_le_exp.mpr hexponent
    _ = Real.exp 2 / (p : ℝ) := by
      rw [Real.exp_sub, Real.exp_log hpR]

/-- The complete source-shaped radial displacement through `y`, before the
final bounded-Mertens scalar simplification. -/
theorem sum_prime_radial_norm_sub_sourceLow_le
    {y : ℕ} {sigmaLow sigmaHigh t : ℝ}
    (hle : sigmaLow ≤ sigmaHigh)
    (hsigma : 1 - 2 / Real.log (y : ℝ) ≤ sigmaLow) :
    (∑ p ∈ primesUpTo y,
      (‖(p : ℂ) ^ (-((sigmaLow : ℂ) + Complex.I * (t : ℂ)))‖ -
        ‖(p : ℂ) ^ (-((sigmaHigh : ℂ) + Complex.I * (t : ℂ)))‖)) ≤
      Real.exp 2 * (sigmaHigh - sigmaLow) * primeLogHarmonicSum y := by
  apply sum_prime_radial_norm_sub_le_mul_primeLogHarmonicSum hle
  intro p hp
  exact norm_prime_cpow_sourceLow_le_exp_two_div
    (mem_primesUpTo.mp hp).1 (mem_primesUpTo.mp hp).2 hsigma

/-- Under the exact A.10 gap `≤ 3 / log y`, the entire horizontal shift
has an absolute cost. -/
theorem sum_prime_radial_norm_sub_sourceGap_le_constant
    {y : ℕ} (hy : 2 ≤ y) {sigmaLow sigmaHigh t : ℝ}
    (hle : sigmaLow ≤ sigmaHigh)
    (hsigma : 1 - 2 / Real.log (y : ℝ) ≤ sigmaLow)
    (hgap : sigmaHigh - sigmaLow ≤ 3 / Real.log (y : ℝ)) :
    (∑ p ∈ primesUpTo y,
      (‖(p : ℂ) ^ (-((sigmaLow : ℂ) + Complex.I * (t : ℂ)))‖ -
        ‖(p : ℂ) ^ (-((sigmaHigh : ℂ) + Complex.I * (t : ℂ)))‖)) ≤
      3 * Real.exp 2 *
        (1 + primeLogMertensConstant / Real.log 2) := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hyR : (2 : ℝ) ≤ y := by exact_mod_cast hy
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (lt_of_lt_of_le (by norm_num) hyR)
  have hlogle : Real.log 2 ≤ Real.log (y : ℝ) :=
    Real.log_le_log (by norm_num) hyR
  have hPH0 : 0 ≤ primeLogHarmonicSum y := by
    unfold primeLogHarmonicSum
    apply Finset.sum_nonneg
    intro p hp
    have hpPrime : p.Prime := by
      have hp' : p ≤ y ∧ p.Prime := by
        simpa [Nat.primesLE_eq_filter_range] using hp
      exact hp'.2
    exact div_nonneg
      (Real.log_nonneg (by exact_mod_cast hpPrime.one_le)) (by positivity)
  have hPH : primeLogHarmonicSum y ≤
      Real.log (y : ℝ) + primeLogMertensConstant := by
    have hs := primeLogMertensConstant_spec y
    linarith [le_abs_self (primeLogHarmonicSum y - Real.log y)]
  have hCdiv : primeLogMertensConstant / Real.log (y : ℝ) ≤
      primeLogMertensConstant / Real.log 2 := by
    exact div_le_div_of_nonneg_left primeLogMertensConstant_nonneg
      hlogTwo hlogle
  calc
    (∑ p ∈ primesUpTo y,
      (‖(p : ℂ) ^ (-((sigmaLow : ℂ) + Complex.I * (t : ℂ)))‖ -
        ‖(p : ℂ) ^ (-((sigmaHigh : ℂ) + Complex.I * (t : ℂ)))‖)) ≤
        Real.exp 2 * (sigmaHigh - sigmaLow) * primeLogHarmonicSum y :=
      sum_prime_radial_norm_sub_sourceLow_le hle hsigma
    _ ≤ Real.exp 2 * (3 / Real.log (y : ℝ)) *
        (Real.log (y : ℝ) + primeLogMertensConstant) := by
      gcongr
    _ = 3 * Real.exp 2 *
        (1 + primeLogMertensConstant / Real.log (y : ℝ)) := by
      field_simp
    _ ≤ 3 * Real.exp 2 *
        (1 + primeLogMertensConstant / Real.log 2) := by
      gcongr

/-- Specialization of the paired finite-product shift to the two source
vertical lines.  The same radial displacement occurs in the actual and
positive products, hence the factor `12`. -/
theorem mul_norm_prod_gsA9LocalEulerFactor_source_shift_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime)
    {sigmaLow sigmaHigh t D : ℝ} (hle : sigmaLow ≤ sigmaHigh)
    (hthird : ∀ p ∈ S,
      ‖(p : ℂ) ^ (-((sigmaLow : ℂ) + Complex.I * (t : ℂ)))‖ ≤ (1 / 3 : ℝ))
    (hD : (∑ p ∈ S,
      (‖(p : ℂ) ^ (-((sigmaLow : ℂ) + Complex.I * (t : ℂ)))‖ -
        ‖(p : ℂ) ^ (-((sigmaHigh : ℂ) + Complex.I * (t : ℂ)))‖)) ≤ D) :
    let one : ℕ → ℂ := fun _ ↦ 1
    ‖∏ p ∈ S, gsA9LocalEulerFactor f
        ((sigmaLow : ℂ) + Complex.I * (t : ℂ)) p‖ *
      ‖∏ p ∈ S, gsA9LocalEulerFactor one (sigmaLow : ℂ) p‖ ≤
      (‖∏ p ∈ S, gsA9LocalEulerFactor f
          ((sigmaHigh : ℂ) + Complex.I * (t : ℂ)) p‖ *
        ‖∏ p ∈ S, gsA9LocalEulerFactor one (sigmaHigh : ℂ) p‖) *
        Real.exp (12 * D) := by
  dsimp only
  let sLow : ℂ := (sigmaLow : ℂ) + Complex.I * (t : ℂ)
  let sHigh : ℂ := (sigmaHigh : ℂ) + Complex.I * (t : ℂ)
  let srLow : ℂ := (sigmaLow : ℂ)
  let srHigh : ℂ := (sigmaHigh : ℂ)
  let c : ℕ → ℝ := fun p ↦ (p : ℝ) ^ (sigmaHigh - sigmaLow)
  have hc : ∀ p ∈ S, 1 ≤ c p := by
    intro p hp
    exact Real.one_le_rpow (by exact_mod_cast (hprime p hp).one_le)
      (sub_nonneg.mpr hle)
  have hfactor : ∀ p ∈ S,
      (p : ℂ) ^ (-sLow) = (c p : ℂ) * (p : ℂ) ^ (-sHigh) := by
    intro p hp
    exact nat_cpow_neg_low_eq_rpow_gap_mul_neg_high (hprime p hp) hle
  have hfactorp : ∀ p ∈ S,
      (p : ℂ) ^ (-srLow) = (c p : ℂ) * (p : ℂ) ^ (-srHigh) := by
    intro p hp
    have h := nat_cpow_neg_low_eq_rpow_gap_mul_neg_high
      (hprime p hp) (t := 0) hle
    simpa only [mul_zero, Complex.ofReal_zero, add_zero, sLow, sHigh, srLow, srHigh, c]
      using h
  have hnormLow (p : ℕ) (hp : p.Prime) :
      ‖(p : ℂ) ^ (-sLow)‖ = ‖(p : ℂ) ^ (-srLow)‖ := by
    rw [show sLow = (sigmaLow : ℂ) + Complex.I * (t : ℂ) by rfl,
      Erdos67b.HalaszCpowDeficit.norm_nat_cpow_neg_sigma_add_I_mul hp.pos,
      show srLow = (sigmaLow : ℂ) by rfl,
      Erdos67b.EulerQuantitative.norm_prime_cpow_neg_real sigmaLow ⟨p, hp⟩]
  have hnormHigh (p : ℕ) (hp : p.Prime) :
      ‖(p : ℂ) ^ (-sHigh)‖ = ‖(p : ℂ) ^ (-srHigh)‖ := by
    rw [show sHigh = (sigmaHigh : ℂ) + Complex.I * (t : ℂ) by rfl,
      Erdos67b.HalaszCpowDeficit.norm_nat_cpow_neg_sigma_add_I_mul hp.pos,
      show srHigh = (sigmaHigh : ℂ) by rfl,
      Erdos67b.EulerQuantitative.norm_prime_cpow_neg_real sigmaHigh ⟨p, hp⟩]
  have hthirdp : ∀ p ∈ S, ‖(p : ℂ) ^ (-srLow)‖ ≤ (1 / 3 : ℝ) := by
    intro p hp
    rw [← hnormLow p (hprime p hp)]
    exact hthird p hp
  have hsumEq :
      (∑ p ∈ S, (‖(p : ℂ) ^ (-srLow)‖ - ‖(p : ℂ) ^ (-srHigh)‖)) =
        ∑ p ∈ S, (‖(p : ℂ) ^ (-sLow)‖ - ‖(p : ℂ) ^ (-sHigh)‖) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [hnormLow p (hprime p hp), hnormHigh p (hprime p hp)]
  have hpair := mul_norm_prod_gsA9LocalEulerFactor_shift_le_exp_sum_norm_sub
    hmul hbound S hprime c c hc hc hfactor hfactorp
      (by simpa only [sLow] using hthird) hthirdp
  let E : ℝ := ∑ p ∈ S, (‖(p : ℂ) ^ (-sLow)‖ - ‖(p : ℂ) ^ (-sHigh)‖)
  have hED : E ≤ D := by simpa only [E, sLow, sHigh] using hD
  calc
    ‖∏ p ∈ S, gsA9LocalEulerFactor f sLow p‖ *
        ‖∏ p ∈ S, gsA9LocalEulerFactor (fun _ ↦ 1) srLow p‖ ≤
      (‖∏ p ∈ S, gsA9LocalEulerFactor f sHigh p‖ *
        ‖∏ p ∈ S, gsA9LocalEulerFactor (fun _ ↦ 1) srHigh p‖) *
        Real.exp (6 * (E + E)) := by
      simpa only [hsumEq, E] using hpair
    _ ≤ (‖∏ p ∈ S, gsA9LocalEulerFactor f sHigh p‖ *
        ‖∏ p ∈ S, gsA9LocalEulerFactor (fun _ ↦ 1) srHigh p‖) *
        Real.exp (12 * D) := by
      apply mul_le_mul_of_nonneg_left
      · apply Real.exp_le_exp.mpr
        linarith
      · exact mul_nonneg (norm_nonneg _) (norm_nonneg _)

end

end Erdos67b.MRHalaszBands
