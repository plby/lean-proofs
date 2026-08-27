/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPrimeProgressionEnvelope

/-!
# A power-log majorant for the Vaughan remainder at cube-root level

All conductor and modulus cutoffs remain free. The sixth-root identities
already proved for the Vaughan estimate keep the polynomial comparisons exact.
-/

namespace Erdos4b.FGKMT

noncomputable section

open BoundedGaps.Maynard

theorem vaughanSixthRoot_fifth_eq_rpow (x : ℕ) :
    vaughanSixthRoot x ^ 5 = (x : ℝ) ^ (5 / 6 : ℝ) := by
  unfold vaughanSixthRoot
  calc
    Real.rpow (x : ℝ) (1 / 6 : ℝ) ^ 5 =
        Real.rpow (Real.rpow (x : ℝ) (1 / 6 : ℝ)) (5 : ℝ) :=
      (Real.rpow_natCast _ 5).symm
    _ = Real.rpow (x : ℝ) ((1 / 6 : ℝ) * 5) :=
      (Real.rpow_mul (Nat.cast_nonneg x) (1 / 6 : ℝ) 5).symm
    _ = _ := by norm_num

theorem sqrt_mul_cubeRange_le {x L : ℕ} (hL : (L : ℝ) ≤ vaughanCubeRoot x) :
    Real.sqrt (x : ℝ) * L ≤ vaughanSixthRoot x ^ 5 := by
  rw [vaughanSixthRoot_pow_five]
  exact mul_le_mul_of_nonneg_left hL (Real.sqrt_nonneg _)

theorem cubeRoot_sq_mul_sqrt_cubeRange_le {x L : ℕ}
    (hL : (L : ℝ) ≤ vaughanCubeRoot x) :
    vaughanCubeRoot x ^ 2 * Real.sqrt (L : ℝ) ≤ vaughanSixthRoot x ^ 5 := by
  have hsqrt := Real.sqrt_le_sqrt hL
  rw [← vaughanSixthRoot_sq, Real.sqrt_sq (vaughanSixthRoot_nonneg x)] at hsqrt
  calc
    _ ≤ vaughanCubeRoot x ^ 2 * vaughanSixthRoot x :=
      mul_le_mul_of_nonneg_left hsqrt (sq_nonneg _)
    _ = _ := by rw [← vaughanSixthRoot_sq]; ring

theorem vaughanAbelEnvelope_le_cubeRange {x L R : ℕ} (hx : 1 ≤ x)
    (hR : 1 ≤ R) (hRL : R ≤ L) (hL : (L : ℝ) ≤ vaughanCubeRoot x) :
    vaughanPrimitiveMeanAbelEnvelope x R L ≤
      4 * (x : ℝ) / R + 27 * (vaughanSixthRoot x ^ 5) * (1 + Real.log (x : ℝ)) := by
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hR.trans hRL
  have hRpos : (0 : ℝ) < R := zero_lt_one.trans_le hR1
  have hLpos : (0 : ℝ) < L := zero_lt_one.trans_le hL1
  have hLx : (L : ℝ) ≤ x :=
    (hL.trans (vaughanCubeRoot_le_sqrt hx)).trans
      (Real.sqrt_le_self_iff.mpr (Or.inr hx1))
  have hlogL : Real.log (L : ℝ) ≤ Real.log (x : ℝ) := Real.log_le_log hLpos hLx
  have hlogRatio : Real.log (Real.exp 1 * (L : ℝ) / R) ≤ 1 + Real.log (x : ℝ) := by
    have hdiv : (L : ℝ) / R ≤ L := div_le_self hLpos.le hR1
    have hlogDiv := Real.log_le_log (div_pos hLpos hRpos) hdiv
    rw [show Real.exp 1 * (L : ℝ) / R = Real.exp 1 * ((L : ℝ) / R) by ring,
      Real.log_mul (Real.exp_ne_zero 1) (div_pos hLpos hRpos).ne', Real.log_exp]
    linarith
  have hsecond := sqrt_mul_cubeRange_le hL
  have hthird := cubeRoot_sq_mul_sqrt_cubeRange_le hL
  have hfourth := mul_le_mul_of_nonneg_left hlogRatio
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5) (mul_nonneg (Real.sqrt_nonneg (x : ℝ))
      (vaughanCubeRoot_nonneg x)))
  rw [← vaughanSixthRoot_pow_five] at hfourth
  have hlog0 := Real.log_natCast_nonneg x
  have hP : 0 ≤ vaughanSixthRoot x ^ 5 := pow_nonneg (vaughanSixthRoot_nonneg x) _
  unfold vaughanPrimitiveMeanAbelEnvelope
  rw [← vaughanSixthRoot_pow_five]
  nlinarith [mul_nonneg hP hlog0]

theorem vaughanLogPower_le_fifth {x : ℕ} (hlog : 1 ≤ Real.log (x : ℝ)) :
    vaughanPrimitiveMeanEquationOneTwoLogPower x ≤ Real.log (x : ℝ) ^ 5 := by
  have hsqrt := Real.sqrt_le_self_iff.mpr (Or.inr hlog)
  unfold vaughanPrimitiveMeanEquationOneTwoLogPower
  calc
    _ ≤ Real.log (x : ℝ) ^ 4 * Real.log (x : ℝ) :=
      mul_le_mul_of_nonneg_left hsqrt (by positivity)
    _ = _ := by ring

theorem exists_primeProgressionVaughanRemainder_le_pow_log :
    ∃ K : ℝ, 0 < K ∧ ∀ x L R : ℕ, 1 ≤ x → 1 ≤ Real.log (x : ℝ) →
      1 ≤ R → R ≤ L → (L : ℝ) ≤ vaughanCubeRoot x →
      primeProgressionVaughanRemainder L R x ≤ K *
        ((x : ℝ) / R * Real.log (x : ℝ) ^ 5 +
          (x : ℝ) ^ (5 / 6 : ℝ) * Real.log (x : ℝ) ^ 6) := by
  let V := 5 * vaughanPrimitiveMeanEquationOneOneConstant (Real.log 4 + 4)
  have hV : 0 ≤ V := mul_nonneg (by norm_num)
    (vaughanPrimitiveMeanEquationOneOneConstant_nonneg _)
  refine ⟨58 * V + 6, by positivity, ?_⟩
  intro x L R hx hlog hR hRL hL
  let ell := Real.log (x : ℝ)
  let P := vaughanSixthRoot x ^ 5
  have hell : 1 ≤ ell := hlog
  have hell0 : 0 ≤ ell := zero_le_one.trans hell
  have hP : 0 ≤ P := pow_nonneg (vaughanSixthRoot_nonneg x) _
  have hXdiv : 0 ≤ (x : ℝ) / R := by positivity
  have hLx : (L : ℝ) ≤ x := (hL.trans (vaughanCubeRoot_le_sqrt hx)).trans
    (Real.sqrt_le_self_iff.mpr (Or.inr (by exact_mod_cast hx)))
  have hLP : (L : ℝ) ≤ P := by
    apply hL.trans
    rw [← vaughanSixthRoot_sq]
    exact pow_le_pow_right₀ (one_le_vaughanSixthRoot hx) (by norm_num)
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have hlogProduct : Real.log ((L * x : ℕ) : ℝ) ≤ 2 * ell := by
    rw [Nat.cast_mul, Real.log_mul hLpos.ne' hxpos.ne']
    have := Real.log_le_log hLpos hLx
    dsimp [ell]
    linarith
  have hlogSq : Real.log ((L * x : ℕ) : ℝ) ^ 2 ≤ 4 * ell ^ 2 := by
    have := pow_le_pow_left₀ (Real.log_natCast_nonneg (L * x)) hlogProduct 2
    nlinarith
  have helementary : (L : ℝ) * Real.log ((L * x : ℕ) : ℝ) ^ 2 ≤ 4 * P * ell ^ 2 := by
    have := mul_le_mul hLP hlogSq (sq_nonneg _) hP
    nlinarith
  have hprimePower : 2 * (L : ℝ) * Real.sqrt (x : ℝ) * ell ≤ 2 * P * ell := by
    have := mul_le_mul_of_nonneg_right (sqrt_mul_cubeRange_le hL) hell0
    dsimp [P] at *
    nlinarith
  have habel := vaughanAbelEnvelope_le_cubeRange hx hR hRL hL
  have hlogPower := vaughanLogPower_le_fifth hlog
  have hproduct : vaughanPrimitiveMeanAbelEnvelope x R L *
      vaughanPrimitiveMeanEquationOneTwoLogPower x ≤
      4 * ((x : ℝ) / R * ell ^ 5) + 54 * (P * ell ^ 6) := by
    calc
      _ ≤ (4 * (x : ℝ) / R + 27 * P * (1 + ell)) * ell ^ 5 :=
        mul_le_mul habel hlogPower (vaughanPrimitiveMeanEquationOneTwoLogPower_nonneg x)
          (by positivity)
      _ ≤ (4 * (x : ℝ) / R + 54 * P * ell) * ell ^ 5 := by
        have hPell : 27 * P * (1 + ell) ≤ 54 * P * ell := by
          nlinarith [mul_nonneg hP (sub_nonneg.mpr hell)]
        exact mul_le_mul_of_nonneg_right (add_le_add le_rfl hPell) (pow_nonneg hell0 _)
      _ = _ := by ring
  have hpow16 : ell ≤ ell ^ 6 := by simpa using pow_le_pow_right₀ hell (by norm_num : 1 ≤ 6)
  have hpow26 : ell ^ 2 ≤ ell ^ 6 := pow_le_pow_right₀ hell (by norm_num)
  have hcost1 := mul_le_mul_of_nonneg_left hpow16 hP
  have hcost2 := mul_le_mul_of_nonneg_left hpow26 hP
  have hcostV := mul_le_mul_of_nonneg_left hproduct hV
  have hleftPos : 0 ≤ (x : ℝ) / R * ell ^ 5 := by positivity
  have hrightPos : 0 ≤ P * ell ^ 6 := by positivity
  rw [← vaughanSixthRoot_fifth_eq_rpow]
  change primeProgressionVaughanRemainder L R x ≤
    (58 * V + 6) * ((x : ℝ) / R * ell ^ 5 + P * ell ^ 6)
  dsimp [primeProgressionVaughanRemainder]
  change (L : ℝ) * Real.log ((L * x : ℕ) : ℝ) ^ 2 +
    V * vaughanPrimitiveMeanAbelEnvelope x R L *
      vaughanPrimitiveMeanEquationOneTwoLogPower x +
        2 * (L : ℝ) * Real.sqrt (x : ℝ) * ell ≤ _
  nlinarith [mul_nonneg hV hleftPos, mul_nonneg hV hrightPos]

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.vaughanAbelEnvelope_le_cubeRange
#print axioms Erdos4b.FGKMT.exists_primeProgressionVaughanRemainder_le_pow_log
