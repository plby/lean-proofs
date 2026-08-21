import ErdosProblems.Erdos239.External.Erdos67.MRGSA10AlternatingLowNorm
import ErdosProblems.Erdos239.External.Erdos67.MRGSA10TailoredNearMass
import ErdosProblems.Erdos239.External.Erdos67.MRGSA10NearWeightAverage

/-!
# The joint high-factor average in the A.10 rectangle

The two Mangoldt factors must be averaged together with the shifted high
factor.  At a fixed high integer `H`, the alpha integral produces
`1 / log H`, while the beta integral produces `1 / (2 log (H / a))`.
The two von-Mangoldt divisor identities cancel these denominators exactly.
This is the finite joint estimate which is lost if the two distinguished
prime-power variables are estimated separately.
-/

open scoped BigOperators
open Finset MeasureTheory Set

namespace Erdos67.MRHalaszBands

noncomputable section

private theorem doubleIntervalIntegral_finsetSum
    {ι : Type*} {s : Finset ι} {eta : ℝ} {F : ι → ℝ → ℝ → ℝ}
    (hF : ∀ i ∈ s, Continuous (Function.uncurry (F i))) :
    (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta, ∑ i ∈ s, F i alpha beta) =
      ∑ i ∈ s, ∫ alpha : ℝ in 0..eta,
        ∫ beta : ℝ in 0..eta, F i alpha beta := by
  have hinner (i : ι) (hi : i ∈ s) : Continuous (fun alpha : ℝ ↦
      ∫ beta : ℝ in 0..eta, F i alpha beta) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact hF i hi
  have hinnerSum : ∀ alpha : ℝ,
      (∫ beta : ℝ in 0..eta, ∑ i ∈ s, F i alpha beta) =
        ∑ i ∈ s, ∫ beta : ℝ in 0..eta, F i alpha beta := by
    intro alpha
    apply intervalIntegral.integral_finsetSum
    intro i hi
    exact ((hF i hi).comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable 0 eta
  simp_rw [hinnerSum]
  apply intervalIntegral.integral_finsetSum
  intro i hi
  exact (hinner i hi).intervalIntegrable 0 eta

/-- The positive three-factor high majorant, ordered as
`H = a*(b*e)`.  This association is the one for which the beta integral
and the inner Mangoldt divisor identity cancel without loss. -/
def gsA10JointHighMajorant (H : ℕ) (alpha beta : ℝ) : ℝ :=
  ∑ aq ∈ H.divisorsAntidiagonal,
    ∑ be ∈ aq.2.divisorsAntidiagonal,
      Real.exp (-alpha * Real.log (aq.1 : ℝ)) *
        ArithmeticFunction.vonMangoldt aq.1 *
        (Real.exp (-(alpha + 2 * beta) * Real.log (be.1 : ℝ)) *
          ArithmeticFunction.vonMangoldt be.1) *
        Real.exp (-(alpha + 2 * beta) * Real.log (be.2 : ℝ))

theorem gsA10JointHighMajorant_nonneg
    (H : ℕ) (alpha beta : ℝ) :
    0 ≤ gsA10JointHighMajorant H alpha beta := by
  unfold gsA10JointHighMajorant
  positivity

private theorem exp_three_shift_eq
    {a b e : ℕ} (ha : 0 < a) (hb : 0 < b) (he : 0 < e)
    (alpha beta : ℝ) :
    Real.exp (-alpha * Real.log (a : ℝ)) *
          ArithmeticFunction.vonMangoldt a *
        (Real.exp (-(alpha + 2 * beta) * Real.log (b : ℝ)) *
          ArithmeticFunction.vonMangoldt b) *
        Real.exp (-(alpha + 2 * beta) * Real.log (e : ℝ)) =
      (ArithmeticFunction.vonMangoldt a *
          ArithmeticFunction.vonMangoldt b) *
        (Real.exp (-alpha * Real.log (a : ℝ)) *
          Real.exp (-(alpha + 2 * beta) * Real.log ((b * e : ℕ) : ℝ))) := by
  have hlog : Real.log (((b * e : ℕ) : ℝ)) =
      Real.log (b : ℝ) + Real.log (e : ℝ) := by
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hb.ne')
      (by exact_mod_cast he.ne')]
  rw [hlog, show -(alpha + 2 * beta) *
      (Real.log (b : ℝ) + Real.log (e : ℝ)) =
      (-(alpha + 2 * beta) * Real.log (b : ℝ)) +
        (-(alpha + 2 * beta) * Real.log (e : ℝ)) by ring,
    Real.exp_add]
  ring

private theorem jointHigh_term_average_le
    {a b e : ℕ} (ha : 0 < a) (hb : 0 < b) (he : 0 < e)
    {eta : ℝ} (heta : 0 ≤ eta) :
    (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta,
        Real.exp (-alpha * Real.log (a : ℝ)) *
            ArithmeticFunction.vonMangoldt a *
          (Real.exp (-(alpha + 2 * beta) * Real.log (b : ℝ)) *
            ArithmeticFunction.vonMangoldt b) *
          Real.exp (-(alpha + 2 * beta) * Real.log (e : ℝ))) ≤
      ArithmeticFunction.vonMangoldt a *
        ArithmeticFunction.vonMangoldt b *
          (Real.log ((a * (b * e) : ℕ) : ℝ))⁻¹ *
          (2 * Real.log ((b * e : ℕ) : ℝ))⁻¹ := by
  by_cases hLa : ArithmeticFunction.vonMangoldt a = 0
  · simp [hLa]
  by_cases hLb : ArithmeticFunction.vonMangoldt b = 0
  · simp [hLb]
  have ha2 : 2 ≤ a := by
    by_contra h
    interval_cases a <;> simp_all
  have hb2 : 2 ≤ b := by
    by_contra h
    interval_cases b <;> simp_all
  have hbe2 : 2 ≤ b * e := by nlinarith
  have havg := intervalIntegral_intervalIntegral_exp_natLog_two_shift_le
    (m := a) (n := b * e) ha2 hbe2 heta
  have hlogs : Real.log (a : ℝ) + Real.log ((b * e : ℕ) : ℝ) =
      Real.log ((a * (b * e) : ℕ) : ℝ) := by
    simp only [Nat.cast_mul]
    symm
    exact Real.log_mul (x := (a : ℝ)) (y := ((b : ℝ) * (e : ℝ)))
      (by positivity) (by positivity)
  simp_rw [exp_three_shift_eq ha hb he]
  simp_rw [intervalIntegral.integral_const_mul]
  rw [hlogs] at havg
  have hscaled := mul_le_mul_of_nonneg_left havg
    (mul_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := a))
      (ArithmeticFunction.vonMangoldt_nonneg (n := b)))
  simpa only [intervalIntegral.integral_const_mul, mul_assoc] using hscaled

private theorem jointHigh_reciprocal_sum_le_half
    {H : ℕ} (hH : 0 < H) :
    (∑ aq ∈ H.divisorsAntidiagonal,
      ∑ be ∈ aq.2.divisorsAntidiagonal,
        ArithmeticFunction.vonMangoldt aq.1 *
          ArithmeticFunction.vonMangoldt be.1 *
            (Real.log ((aq.1 * (be.1 * be.2) : ℕ) : ℝ))⁻¹ *
            (2 * Real.log ((be.1 * be.2 : ℕ) : ℝ))⁻¹) ≤ 1 / 2 := by
  by_cases hH1 : H = 1
  · subst H
    norm_num
  have hHlog : 0 < Real.log (H : ℝ) := by
    have hHtwo : 2 ≤ H := by omega
    exact Real.log_pos (by exact_mod_cast (show 1 < H by omega))
  calc
    _ = ∑ aq ∈ H.divisorsAntidiagonal,
        ArithmeticFunction.vonMangoldt aq.1 *
          (Real.log (H : ℝ))⁻¹ *
          (∑ be ∈ aq.2.divisorsAntidiagonal,
            ArithmeticFunction.vonMangoldt be.1 *
              (2 * Real.log (aq.2 : ℝ))⁻¹) := by
      apply Finset.sum_congr rfl
      intro aq haq
      have haqProd := (Nat.mem_divisorsAntidiagonal.mp haq).1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro be hbe
      have hbeProd := (Nat.mem_divisorsAntidiagonal.mp hbe).1
      have hprod : aq.1 * (be.1 * be.2) = H := by
        rw [hbeProd, haqProd]
      rw [hprod, hbeProd]
      ring
    _ ≤ ∑ aq ∈ H.divisorsAntidiagonal,
        ArithmeticFunction.vonMangoldt aq.1 *
          (Real.log (H : ℝ))⁻¹ * (1 / 2) := by
      apply Finset.sum_le_sum
      intro aq haq
      apply mul_le_mul_of_nonneg_left
      · by_cases hq : aq.2 = 1
        · simp [hq]
        have hqpos : 0 < aq.2 := Nat.pos_of_ne_zero
          (Nat.ne_zero_of_mem_divisorsAntidiagonal haq).2
        have hqlog : 0 < Real.log (aq.2 : ℝ) :=
          Real.log_pos (by exact_mod_cast (show 1 < aq.2 by omega))
        rw [Nat.sum_divisorsAntidiagonal
          (fun b _ ↦ ArithmeticFunction.vonMangoldt b *
            (2 * Real.log (aq.2 : ℝ))⁻¹)]
        rw [← Finset.sum_mul]
        rw [ArithmeticFunction.vonMangoldt_sum]
        field_simp
        norm_num
      · exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
          (inv_nonneg.mpr hHlog.le)
    _ = (Real.log (H : ℝ))⁻¹ * (1 / 2) *
          (∑ a ∈ H.divisors, ArithmeticFunction.vonMangoldt a) := by
      rw [Nat.sum_divisorsAntidiagonal
        (fun a _ ↦ ArithmeticFunction.vonMangoldt a *
          (Real.log (H : ℝ))⁻¹ * (1 / 2))]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = 1 / 2 := by
      rw [ArithmeticFunction.vonMangoldt_sum]
      field_simp

/-- The joint alpha-beta average of the whole three-factor high majorant is
at most `1/2`, uniformly in the high integer.  No divisor-count factor is
introduced. -/
theorem doubleIntervalIntegral_gsA10JointHighMajorant_le_half
    {H : ℕ} (hH : 0 < H) {eta : ℝ} (heta : 0 ≤ eta) :
    (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta,
        gsA10JointHighMajorant H alpha beta) ≤ 1 / 2 := by
  -- The proof below first averages every finite divisor term, then uses
  -- the two exact Mangoldt divisor identities.  Terms with quotient one
  -- vanish before a reciprocal logarithm is introduced.
  unfold gsA10JointHighMajorant
  rw [doubleIntervalIntegral_finsetSum]
  · calc
      (∑ aq ∈ H.divisorsAntidiagonal,
        ∫ alpha : ℝ in 0..eta,
          ∫ beta : ℝ in 0..eta,
            ∑ be ∈ aq.2.divisorsAntidiagonal,
              Real.exp (-alpha * Real.log (aq.1 : ℝ)) *
                  ArithmeticFunction.vonMangoldt aq.1 *
                (Real.exp (-(alpha + 2 * beta) * Real.log (be.1 : ℝ)) *
                  ArithmeticFunction.vonMangoldt be.1) *
                Real.exp (-(alpha + 2 * beta) * Real.log (be.2 : ℝ))) ≤
          ∑ aq ∈ H.divisorsAntidiagonal,
            ∑ be ∈ aq.2.divisorsAntidiagonal,
              ArithmeticFunction.vonMangoldt aq.1 *
                ArithmeticFunction.vonMangoldt be.1 *
                  (Real.log ((aq.1 * (be.1 * be.2) : ℕ) : ℝ))⁻¹ *
                  (2 * Real.log ((be.1 * be.2 : ℕ) : ℝ))⁻¹ := by
        apply Finset.sum_le_sum
        intro aq haq
        rw [doubleIntervalIntegral_finsetSum]
        · apply Finset.sum_le_sum
          intro be hbe
          have ha : 0 < aq.1 := Nat.pos_of_ne_zero
            (Nat.ne_zero_of_mem_divisorsAntidiagonal haq).1
          have hb : 0 < be.1 := Nat.pos_of_ne_zero
            (Nat.ne_zero_of_mem_divisorsAntidiagonal hbe).1
          have he : 0 < be.2 := Nat.pos_of_ne_zero
            (Nat.ne_zero_of_mem_divisorsAntidiagonal hbe).2
          exact jointHigh_term_average_le ha hb he heta
        · intro be hbe
          fun_prop
      _ ≤ 1 / 2 := jointHigh_reciprocal_sum_le_half hH
  · intro aq haq
    fun_prop

end

end Erdos67.MRHalaszBands
