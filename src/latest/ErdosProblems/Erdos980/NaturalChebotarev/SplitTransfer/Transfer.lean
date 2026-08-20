import ErdosProblems.Erdos980.NaturalChebotarev.SplitTransfer.Counting
import ErdosProblems.Erdos980.NaturalChebotarev.FiniteException
import ErdosProblems.Erdos980.NaturalChebotarev.PrimeIdealTheorem.PrimeIdealCounting

/-!
# Prime-ideal theorem to completely-split rational primes

The only analytic input to the main theorem is a prime-ideal-theorem
asymptotic for `L`.  The algebraic counting identity and both error estimates
are proved in `Counting`.
-/

namespace Erdos980.NaturalChebotarev.SplitTransfer

open Asymptotics Filter

noncomputable section

variable (L : Type*) [Field L] [NumberField L] [Algebra ℚ L] [IsGalois ℚ L]

private theorem real_sqrt_isLittleO_div_log :
    Real.sqrt =o[atTop] (fun x : ℝ ↦ x / Real.log x) := by
  have hsqrt_log : (fun x : ℝ ↦ Real.sqrt x * Real.log x) =o[atTop]
      (fun x : ℝ ↦ x) :=
    (isLittleO_mul_iff_isLittleO_div (hf := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      exact Real.sqrt_ne_zero'.mpr hx)).mpr (by
        simp_rw [Real.div_sqrt, Real.sqrt_eq_rpow]
        exact isLittleO_log_rpow_atTop one_half_pos)
  have hlog_ne : ∀ᶠ x : ℝ in atTop, Real.log x ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact Real.log_ne_zero_of_pos_of_ne_one (by positivity) (ne_of_gt hx)
  apply (isLittleO_mul_iff_isLittleO_div hlog_ne).mp
  simpa only [mul_comm] using hsqrt_log

/-- `⌊√x⌋ + 1` is negligible on the prime-number-theorem scale. -/
theorem sqrt_add_one_isLittleO_pntMain :
    (fun x : ℕ ↦ (x.sqrt + 1 : ℝ)) =o[atTop]
      (fun x : ℕ ↦ (x : ℝ) / Real.log (x : ℝ)) := by
  have hsqrtReal : (fun x : ℕ ↦ Real.sqrt (x : ℝ)) =o[atTop]
      (fun x : ℕ ↦ (x : ℝ) / Real.log (x : ℝ)) := by
    simpa [Function.comp_def] using
      real_sqrt_isLittleO_div_log.comp_tendsto
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have hfloor : (fun x : ℕ ↦ (x.sqrt : ℝ)) =O[atTop]
      (fun x : ℕ ↦ Real.sqrt (x : ℝ)) := by
    apply Filter.Eventually.isBigO
    filter_upwards with x
    rw [Real.norm_of_nonneg (by positivity)]
    exact Real.nat_sqrt_le_real_sqrt
  have hsqrt := hfloor.trans_isLittleO hsqrtReal
  have hone :=
    Erdos980.NaturalChebotarev.const_isLittleO_natCast_div_log 1
  apply (hsqrt.add hone).congr'
  · exact Eventually.of_forall fun x ↦ by push_cast; ring
  · rfl

/-- The explicit discrepancy between the prime-ideal count and `[L : ℚ]`
times the completely-split rational-prime count is little-oh of `x / log x`. -/
theorem split_count_error_isLittleO_pntMain :
    (fun x : ℕ ↦ (primeIdealCount L x : ℝ) -
      Module.finrank ℚ L * splitPrimeCount L x) =o[atTop]
        (fun x : ℕ ↦ (x : ℝ) / Real.log (x : ℝ)) := by
  let C : ℝ := ramifiedPrimeIdealCount L
  let d : ℝ := Module.finrank ℚ L
  have henv : (fun x : ℕ ↦ C + d * (x.sqrt + 1 : ℝ)) =o[atTop]
      (fun x : ℕ ↦ (x : ℝ) / Real.log (x : ℝ)) :=
    (Erdos980.NaturalChebotarev.const_isLittleO_natCast_div_log C).add
      (sqrt_add_one_isLittleO_pntMain.const_mul_left d)
  have hbound : (fun x : ℕ ↦ (primeIdealCount L x : ℝ) -
      Module.finrank ℚ L * splitPrimeCount L x) =O[atTop]
      (fun x : ℕ ↦ C + d * (x.sqrt + 1 : ℝ)) := by
    apply IsBigO.of_bound 1
    exact Eventually.of_forall fun x ↦ by
      rw [one_mul, Real.norm_eq_abs,
        Real.norm_of_nonneg (by positivity : 0 ≤ C + d * (x.sqrt + 1 : ℝ))]
      simpa [C, d] using
        abs_primeIdealCount_sub_degree_mul_splitPrimeCount_le L x
  exact hbound.trans_isLittleO henv

/-- **Prime-ideal theorem ⇒ completely-split rational-prime theorem.**

For a finite Galois extension `L / ℚ` of degree `d`, a prime-ideal theorem
for `L` implies that rational primes splitting completely in `L` have counting
asymptotic `(1/d) x / log x`. -/
theorem splitPrimeCount_isEquivalent_of_primeIdealTheorem
    (hPIT : (fun x : ℕ ↦ (primeIdealCount L x : ℝ)) ~[atTop]
      (fun x : ℕ ↦ (x : ℝ) / Real.log (x : ℝ))) :
    (fun x : ℕ ↦ (splitPrimeCount L x : ℝ)) ~[atTop]
      (fun x : ℕ ↦ (Module.finrank ℚ L : ℝ)⁻¹ *
        ((x : ℝ) / Real.log (x : ℝ))) := by
  let d : ℝ := Module.finrank ℚ L
  have hdpos : 0 < d := by
    dsimp [d]
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := L)
  have herr := split_count_error_isLittleO_pntMain L
  have hdSplit : (fun x : ℕ ↦ d * (splitPrimeCount L x : ℝ)) ~[atTop]
      (fun x : ℕ ↦ (x : ℝ) / Real.log (x : ℝ)) := by
    apply (hPIT.sub_isLittleO herr).congr_left
    exact Eventually.of_forall fun x ↦ by
      dsimp [d]
      ring
  have hinv : (fun _ : ℕ ↦ d⁻¹) ~[atTop] (fun _ : ℕ ↦ d⁻¹) :=
    IsEquivalent.refl
  have hscaled := hinv.mul hdSplit
  refine (hscaled.congr_left ?_).congr_right ?_
  · exact Eventually.of_forall fun x ↦ by
      dsimp
      field_simp [hdpos.ne']
  · exact Eventually.of_forall fun x ↦ by
      dsimp [d]

/-- **Natural-density theorem for completely split rational primes.**

For every finite Galois number field `L / ℚ`, the number of rational primes at most `x`
that split completely in `L` is asymptotic to
`(1 / [L : ℚ]) * x / log x`.
-/
theorem splitPrimeCount_isEquivalent :
    (fun x : ℕ ↦ (splitPrimeCount L x : ℝ)) ~[atTop]
      (fun x : ℕ ↦ (Module.finrank ℚ L : ℝ)⁻¹ *
        ((x : ℝ) / Real.log (x : ℝ))) :=
  splitPrimeCount_isEquivalent_of_primeIdealTheorem L
    (PrimeIdealTheorem.primeIdealCount_isEquivalent_natCast_div_log L)

end

end Erdos980.NaturalChebotarev.SplitTransfer
