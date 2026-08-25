import ErdosProblems.Erdos67.MRGSA10TwoBlockAtypicalSmallPowerScale
import ErdosProblems.Erdos67.MRGSA10PrimeLambdaBetaDiagonalScalar
import ErdosProblems.Erdos67.MRGSA10HigherPrimePowerMass

/-!
# The higher-prime-power source scalar at the small-power schedule

The fixed source contour leaves one higher-prime-power correction.  The
fourth-power structural cutoff used by the prime row is not quite enough for
this term by itself.  At the actual small-power block schedule the cutoff
eventually dominates the sixth power of `log X`; this makes the complete HPP
rectangle factor uniformly bounded.
-/

open Filter

namespace Erdos67

noncomputable section

/-- The small-power cutoff eventually dominates the sixth power of the
ambient logarithm. -/
theorem eventually_log_pow_six_le_gsA10SmallPowerBlockCutoff :
    ∀ᶠ Z : ℕ in atTop,
      Real.log (Z : ℝ) ^ 6 ≤
        ((2 ^ ((gsA10SmallPowerBlockExponent Z) ^ 2) : ℕ) : ℝ) := by
  have hlittle :=
    isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 500)
  have hcomp := hlittle.comp_tendsto tendsto_natLog_two_natCast_atTop
  have hsmall := hcomp.bound
    (show (0 : ℝ) < Real.log 2 / 64 by positivity)
  filter_upwards
      [hsmall,
       eventually_half_natLog_rpow_le_gsA10SmallPowerBlockExponent,
       tendsto_natLog_two_natCast_atTop.eventually (eventually_ge_atTop 2),
       tendsto_natLog_two_rpow_one_thousandth_atTop.eventually
        (eventually_ge_atTop 16)]
      with Z hlogSmall hfloor hLtwo hrLarge
  let L : ℝ := Nat.log 2 Z
  let K : ℕ := gsA10SmallPowerBlockExponent Z
  let r : ℝ := L ^ (1 / 1000 : ℝ)
  have hLpos : 0 < L := by
    exact zero_lt_two.trans_le (by simpa only [L] using hLtwo)
  have hKlower : r / 2 ≤ (K : ℝ) := by
    have hf := hfloor
    dsimp only [K, L, r] at hf ⊢
    nlinarith
  have hrSq : r ^ 2 = L ^ (1 / 500 : ℝ) := by
    dsimp only [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]
    norm_num
  have hlogSmallTotal : Real.log 64 + 6 * Real.log L ≤
      Real.log 2 * (r / 2) ^ 2 := by
    have hrLarge' : (16 : ℝ) ≤ r := by simpa only [r, L] using hrLarge
    have hlog64 : Real.log 64 = 6 * Real.log 2 := by
      rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
      norm_num
    have hlogTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    rw [hlog64]
    have hmain : 6 * Real.log L ≤
        (3 * Real.log 2 / 32) * r ^ 2 := by
      have hnorm : |Real.log L| ≤
          (Real.log 2 / 64) * |L ^ (1 / 500 : ℝ)| := by
        simpa only [Function.comp_apply, L, Real.norm_eq_abs] using hlogSmall
      have hpowpos : 0 < L ^ (1 / 500 : ℝ) :=
        Real.rpow_pos_of_pos hLpos _
      have hlogLe : Real.log L ≤
          (Real.log 2 / 64) * L ^ (1 / 500 : ℝ) :=
        (le_abs_self _).trans (hnorm.trans_eq (by rw [abs_of_pos hpowpos]))
      rw [← hrSq] at hlogLe
      nlinarith
    nlinarith [sq_nonneg (r - 16)]
  have hZne : Z ≠ 0 := by
    intro hZ
    subst Z
    simp [L] at hLpos
  have hlogZ : Real.log (Z : ℝ) ≤ 2 * L := by
    let Ln : ℕ := Nat.log 2 Z
    have hpowUpper : Z < 2 ^ (Ln + 1) :=
      Nat.lt_pow_succ_log_self (by omega) Z
    have hmono : Real.log (Z : ℝ) ≤
        Real.log (((2 ^ (Ln + 1) : ℕ) : ℝ)) := by
      apply Real.strictMonoOn_log.monotoneOn
      · simp only [Set.mem_Ioi]
        exact_mod_cast (Nat.pos_of_ne_zero hZne)
      · simp only [Set.mem_Ioi]
        positivity
      · exact_mod_cast hpowUpper.le
    calc
      Real.log (Z : ℝ) ≤ Real.log (((2 ^ (Ln + 1) : ℕ) : ℝ)) := hmono
      _ = ((Ln + 1 : ℕ) : ℝ) * Real.log 2 := by
        rw [Nat.cast_pow, Real.log_pow]
        norm_num
      _ ≤ 2 * L := by
        have hlogTwo : Real.log 2 ≤ 1 := by
          have h := Real.log_le_sub_one_of_pos (x := 2) (by norm_num)
          norm_num at h ⊢
          exact h
        have hLoneR : (1 : ℝ) ≤ L :=
          one_le_two.trans (by simpa only [L] using hLtwo)
        dsimp only [Ln, L]
        norm_num
        nlinarith
  have hlogZpos : 0 ≤ Real.log (Z : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hZne))
  have hlogPow : Real.log (Z : ℝ) ^ 6 ≤
      Real.exp (Real.log 64 + 6 * Real.log L) := by
    calc
      Real.log (Z : ℝ) ^ 6 ≤ (2 * L) ^ 6 :=
        pow_le_pow_left₀ hlogZpos hlogZ 6
      _ = Real.exp (Real.log 64 + 6 * Real.log L) := by
        symm
        rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 64)]
        have hexp : Real.exp (6 * Real.log L) = L ^ 6 := by
          calc
            Real.exp (6 * Real.log L) = Real.exp (Real.log (L ^ 6)) := by
              congr 1
              rw [Real.log_pow]
              norm_num
            _ = L ^ 6 := Real.exp_log (pow_pos hLpos 6)
        rw [hexp]
        ring
  have hKsq : (r / 2) ^ 2 ≤ (K : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hKlower 2
  calc
    Real.log (Z : ℝ) ^ 6 ≤
        Real.exp (Real.log 64 + 6 * Real.log L) := hlogPow
    _ ≤ Real.exp (Real.log 2 * (r / 2) ^ 2) :=
      Real.exp_le_exp.mpr hlogSmallTotal
    _ ≤ Real.exp (Real.log 2 * (K : ℝ) ^ 2) := by
      gcongr
    _ = ((2 ^ (K ^ 2) : ℕ) : ℝ) := by
      rw [mul_comm, show (K : ℝ) ^ 2 = ((K ^ 2 : ℕ) : ℝ) by norm_num,
        Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num
    _ = ((2 ^ ((gsA10SmallPowerBlockExponent Z) ^ 2) : ℕ) : ℝ) := rfl

namespace MRHalaszBands

/-- A fixed bound for the whole higher-prime-power bracket in the normalized
source rectangle. -/
def gsA10SourceHPPRectangleBound : ℝ :=
  96 * gsA10PrimeLambdaHarmonicLogConstant + 576

theorem gsA10SourceHPPRectangleBound_nonneg :
    0 ≤ gsA10SourceHPPRectangleBound := by
  unfold gsA10SourceHPPRectangleBound
  exact add_nonneg
    (mul_nonneg (by norm_num) gsA10PrimeLambdaHarmonicLogConstant_nonneg)
    (by norm_num)

/-- Sixth-power cutoff absorption of the HPP term appearing in
`normalized_doubleIntervalIntegral_norm_sourceTailoredPerron_le`. -/
theorem gsA10SourceHPPRectangleFactor_le
    {y X : ℕ} (hX : 2 ≤ X) (hy : 3 ≤ y)
    (hlog : 1 ≤ Real.log (X : ℝ))
    (hprime : PrimeEstimates.primeReciprocals X ≤ Real.log (X : ℝ))
    (hlogSix : Real.log (X : ℝ) ^ 6 ≤ (y : ℝ)) :
    4 * Real.log (X : ℝ) ^ 2 *
        (2 * gsA10PrimeLambdaHarmonicBudget X *
              gsA10HigherPrimePowerGeometricMass y X +
          (gsA10HigherPrimePowerGeometricMass y X) ^ 2) *
        (Real.log (y : ℝ))⁻¹ ≤
      gsA10SourceHPPRectangleBound := by
  let L : ℝ := Real.log (X : ℝ)
  let H : ℝ := gsA10PrimeLambdaHarmonicBudget X
  let G : ℝ := gsA10HigherPrimePowerGeometricMass y X
  let C : ℝ := gsA10PrimeLambdaHarmonicLogConstant
  have hLpos : 0 < L := zero_lt_one.trans_le (by simpa only [L] using hlog)
  have hypos : (0 : ℝ) < y := by positivity
  have hlogy : 1 ≤ Real.log (y : ℝ) := by
    have hloge : (1 : ℝ) < Real.log 3 := by
      rw [← Real.exp_lt_exp, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
      exact Real.exp_one_lt_three
    exact hloge.le.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hy))
  have heta : (Real.log (y : ℝ))⁻¹ ≤ 1 := by
    simpa only [inv_one] using inv_anti₀ (by linarith : (0 : ℝ) < 1) hlogy
  have hH0 : 0 ≤ H := by
    dsimp only [H, gsA10PrimeLambdaHarmonicBudget]
    positivity
  have hG0 : 0 ≤ G := by
    dsimp only [G, gsA10HigherPrimePowerGeometricMass]
    apply Finset.sum_nonneg
    intro p hp
    apply mul_nonneg
    · exact Real.log_nonneg (by
        have hpPrime := (mem_primesUpTo.mp (Finset.mem_filter.mp hp).1).1
        exact_mod_cast hpPrime.one_le)
    · apply Finset.sum_nonneg
      intro k hk
      exact div_nonneg (sub_nonneg.mpr (one_le_pow₀ (by norm_num)))
        (pow_nonneg (Nat.cast_nonneg _) _)
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    exact gsA10PrimeLambdaHarmonicLogConstant_nonneg
  have hH : H ≤ C * L := by
    simpa only [H, C, L] using gsA10PrimeLambdaHarmonicBudget_le_log hX
  have hmass := gsA10HigherPrimePowerGeometricMass_le (X := X) hy
  have hGfirst : G ≤ 12 * L ^ 2 / (y : ℝ) := by
    calc
      G ≤ 12 * L / (y : ℝ) * PrimeEstimates.primeReciprocals X := by
        simpa only [G, L] using hmass
      _ ≤ 12 * L / (y : ℝ) * L := by
        exact mul_le_mul_of_nonneg_left hprime (by positivity)
      _ = 12 * L ^ 2 / (y : ℝ) := by ring
  have hG : G ≤ 12 / L ^ 4 := by
    calc
      G ≤ 12 * L ^ 2 / (y : ℝ) := hGfirst
      _ ≤ 12 * L ^ 2 / L ^ 6 := by
        exact div_le_div_of_nonneg_left (by positivity) (pow_pos hLpos 6) hlogSix
      _ = 12 / L ^ 4 := by field_simp
  have hHG : L ^ 2 * (2 * H * G) ≤ 24 * C := by
    calc
      L ^ 2 * (2 * H * G) ≤
          L ^ 2 * (2 * (C * L) * (12 / L ^ 4)) := by gcongr
      _ = 24 * C / L := by field_simp; ring
      _ ≤ 24 * C := by
        have hinv : L⁻¹ ≤ 1 := by
          simpa only [inv_one] using inv_anti₀ (by linarith : (0 : ℝ) < 1)
            (by simpa only [L] using hlog)
        rw [div_eq_mul_inv]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hinv
          (mul_nonneg (show (0 : ℝ) ≤ 24 by norm_num) hC0)
  have hGsq : L ^ 2 * G ^ 2 ≤ 144 := by
    calc
      L ^ 2 * G ^ 2 ≤ L ^ 2 * (12 / L ^ 4) ^ 2 := by gcongr
      _ = 144 / L ^ 6 := by field_simp; ring
      _ ≤ 144 := by
        have hpow : 1 ≤ L ^ 6 := one_le_pow₀ (by simpa only [L] using hlog)
        have hinv : (L ^ 6)⁻¹ ≤ 1 := by
          simpa only [inv_one] using inv_anti₀ (by linarith : (0 : ℝ) < 1) hpow
        rw [div_eq_mul_inv]
        nlinarith
  calc
    4 * Real.log (X : ℝ) ^ 2 *
        (2 * gsA10PrimeLambdaHarmonicBudget X *
              gsA10HigherPrimePowerGeometricMass y X +
          (gsA10HigherPrimePowerGeometricMass y X) ^ 2) *
        (Real.log (y : ℝ))⁻¹ =
      4 * (L ^ 2 * (2 * H * G) + L ^ 2 * G ^ 2) *
        (Real.log (y : ℝ))⁻¹ := by
          dsimp only [L, H, G]
          ring
    _ ≤ 4 * (24 * C + 144) * 1 := by gcongr
    _ = gsA10SourceHPPRectangleBound := by
      dsimp only [gsA10SourceHPPRectangleBound, C]
      ring

end MRHalaszBands

end

end Erdos67

#print axioms Erdos67.eventually_log_pow_six_le_gsA10SmallPowerBlockCutoff
#print axioms Erdos67.MRHalaszBands.gsA10SourceHPPRectangleFactor_le
