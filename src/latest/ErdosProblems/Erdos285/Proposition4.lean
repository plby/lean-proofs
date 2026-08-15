/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos285.Analytic
import ErdosProblems.Erdos285.Approximation
import ErdosProblems.Erdos285.PrimePowers
import ErdosProblems.Erdos285.Proposition6Asymptotic
import ErdosProblems.Erdos285.Proposition7
import ErdosProblems.Erdos285.UpperAssembly

/-!
# Martin's Proposition 4 for Erdős Problem 285

This file fixes the asymptotic parameters in the final upper-bound assembly.
The arithmetic constructions are supplied by Propositions 6 and 7 in the
companion files; the lemmas here prove that their correction has negligible
cardinality, that the two denominator ranges are separated, and that the
integer rounding does not change the limiting constant.
-/

namespace Erdos285.Proposition4

open Filter Finset Real
open scoped BigOperators Topology

noncomputable section

/-- The integer fifth-root scale used for the exact correction. -/
def fifthRootFloor (x : ℕ) : ℕ :=
  ⌊(x : ℝ) ^ ((5 : ℝ)⁻¹)⌋₊

@[simp] lemma fifthRootFloor_eq_approximationCorrectionScale (x : ℕ) :
    fifthRootFloor x = approximationCorrectionScale x := rfl

/-- The lower endpoint `e⁻¹ x / 2` of Martin's large-denominator block. -/
def largeLowerCutoff (x : ℕ) : ℕ :=
  ⌊Real.exp (-1) * (x : ℝ) / 2⌋₊

/-- A fixed threshold after which `2 y⁴` lies below `e⁻¹ y⁵/2`. -/
def separationThreshold : ℕ :=
  max 2 ⌈6 * Real.exp 1⌉₊

/-- Pure linear rounding at the limiting density.  The actual Martin cutoff
may include an additional `o(t)` buffer; all later lemmas accept any cutoff
with the same ratio limit. -/
def densityCutoff (t : ℕ) : ℕ :=
  ⌈Analytic.densityConstant * (t : ℝ)⌉₊

/-- A linearly scaled cutoff with an arbitrary vanishing relative buffer. -/
def bufferedCutoff (error : ℕ → ℝ) (t : ℕ) : ℕ :=
  ⌈(Analytic.densityConstant + error t) * (t : ℝ)⌉₊

/-- Martin's explicit vanishing displacement of the lower endpoint.  The
square-root logarithm is slow enough to dominate all quantitative errors in
the filtered initial block, but still tends to zero. -/
def martinMargin (t : ℕ) : ℝ :=
  (Real.sqrt (Real.log (t : ℝ)))⁻¹

/-- A fixed coefficient strictly larger than the square of the limiting
cutoff ratio.  This makes the displaced interval contain a positive
`martinMargin t * t` surplus of terms. -/
def cutoffBufferConstant : ℝ :=
  Analytic.densityConstant ^ 2 + 1

/-- The moving lower endpoint ratio in the final Proposition 6 invocation. -/
def martinLowerRatio (t : ℕ) : ℝ :=
  Real.exp (-1) + martinMargin t

/-- The concrete cutoff used in the final assembly. -/
def martinCutoff (t : ℕ) : ℕ :=
  bufferedCutoff (fun t ↦ cutoffBufferConstant * martinMargin t) t

/-- The rounded fifth-root correction scale attached to `martinCutoff`. -/
def martinCorrectionScale (t : ℕ) : ℕ :=
  fifthRootFloor (martinCutoff t)

/-- The number of terms requested from Proposition 6 after reserving the
exact Proposition 7 correction. -/
def martinMainCount (t : ℕ) : ℕ :=
  mainCount t (martinCorrectionScale t)

/-- The full moving initial block used in the last-crossing construction. -/
def martinInitialBlock (x : ℕ) : Finset ℕ :=
  initialBlockAt (martinLowerRatio x) x

/-- Total term score at cutoff `x`: the full Proposition 6 block together
with the cardinality reserved for Proposition 7. -/
def martinScore (x : ℕ) : ℕ :=
  (martinInitialBlock x).card + correctionCount (fifthRootFloor x)

/-- Reindex a term-count cutoff by the formal statement's `k + 1`. -/
def indexedCutoff (x : ℕ → ℕ) (k : ℕ) : ℕ := x k.succ

@[simp] lemma fifthRootFloor_zero : fifthRootFloor 0 = 0 := by
  simp [fifthRootFloor, Real.zero_rpow (by norm_num : (5 : ℝ)⁻¹ ≠ 0)]

@[simp] lemma martinScore_zero : martinScore 0 = 0 := by
  unfold martinScore
  rw [fifthRootFloor_zero]
  simp [martinInitialBlock, initialBlockAt, initialSmoothBlock,
    martinLowerRatio, martinMargin, correctionCount, primePowerCount]

lemma fifthRootFloor_cast_le (x : ℕ) :
    (fifthRootFloor x : ℝ) ≤ (x : ℝ) ^ ((5 : ℝ)⁻¹) := by
  exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg x) _)

lemma fifthRootFloor_pow_five_le (x : ℕ) :
    fifthRootFloor x ^ 5 ≤ x := by
  have h := pow_le_pow_left₀ (Nat.cast_nonneg (fifthRootFloor x))
    (fifthRootFloor_cast_le x) 5
  have hp : ((x : ℝ) ^ ((5 : ℝ)⁻¹) : ℝ) ^ 5 = x := by
    convert Real.rpow_inv_natCast_pow (Nat.cast_nonneg x)
      (by norm_num : (5 : ℕ) ≠ 0) using 1
    all_goals norm_num
  rw [hp] at h
  exact_mod_cast h

/-- The rounded fifth root increases by at most one in one integer step. -/
lemma fifthRootFloor_succ_le (x : ℕ) :
    fifthRootFloor (x + 1) ≤ fifthRootFloor x + 1 := by
  have hreal : ((x + 1 : ℕ) : ℝ) ^ ((5 : ℝ)⁻¹) ≤
      (x : ℝ) ^ ((5 : ℝ)⁻¹) + 1 := by
    have h := Real.rpow_add_le_add_rpow (a := (x : ℝ)) (b := 1)
      (by positivity) (by norm_num) (by norm_num : (0 : ℝ) ≤ (5 : ℝ)⁻¹)
      (by norm_num : (5 : ℝ)⁻¹ ≤ 1)
    norm_num at h ⊢
    exact h
  rw [fifthRootFloor, fifthRootFloor]
  apply Nat.le_of_lt_succ
  rw [Nat.floor_lt (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  have hlt := Nat.lt_floor_add_one ((x : ℝ) ^ ((5 : ℝ)⁻¹))
  push_cast
  norm_num at hreal ⊢
  linarith

lemma le_fifthRootFloor_of_pow_five_le {q x : ℕ} (hqx : q ^ 5 ≤ x) :
    q ≤ fifthRootFloor x := by
  rw [fifthRootFloor, Nat.le_floor_iff (Real.rpow_nonneg (Nat.cast_nonneg x) _)]
  apply le_of_pow_le_pow_left₀ (by norm_num : (5 : ℕ) ≠ 0)
    (Real.rpow_nonneg (Nat.cast_nonneg x) _)
  have hqxR : (q : ℝ) ^ 5 ≤ (x : ℝ) := by exact_mod_cast hqx
  calc
    (q : ℝ) ^ 5 ≤ (x : ℝ) := hqxR
    _ = ((x : ℝ) ^ ((5 : ℝ)⁻¹)) ^ 5 := by
      symm
      convert Real.rpow_inv_natCast_pow (Nat.cast_nonneg x)
        (by norm_num : (5 : ℕ) ≠ 0) using 1
      all_goals norm_num

lemma primePowerCount_le (y : ℕ) : primePowerCount y ≤ y := by
  rw [primePowerCount]
  calc
    ((Icc 1 y).filter IsPrimePow).card ≤ (Icc 1 y).card := card_filter_le _ _
    _ ≤ y := by simp

lemma primePowerCount_succ_le (y : ℕ) :
    primePowerCount (y + 1) ≤ primePowerCount y + 1 := by
  let A := (Icc 1 (y + 1)).filter IsPrimePow
  let B := (Icc 1 y).filter IsPrimePow
  have hsub : A ⊆ insert (y + 1) B := by
    intro q hq
    simp only [A, B, mem_filter, mem_Icc, Finset.mem_insert] at hq ⊢
    by_cases hqy : q = y + 1
    · exact Or.inl hqy
    · exact Or.inr ⟨⟨hq.1.1, by omega⟩, hq.2⟩
  unfold primePowerCount
  change A.card ≤ B.card + 1
  calc
    A.card ≤ (insert (y + 1) B).card := card_le_card hsub
    _ ≤ B.card + 1 := card_insert_le _ _

lemma correctionCount_le_twice (y : ℕ) : correctionCount y ≤ 2 * y := by
  simpa [correctionCount] using Nat.mul_le_mul_left 2 (primePowerCount_le y)

lemma correctionCount_fifthRoot_succ_le (x : ℕ) :
    correctionCount (fifthRootFloor (x + 1)) ≤
      correctionCount (fifthRootFloor x) + 2 := by
  have hr := fifthRootFloor_succ_le x
  have hp := primePowerCount_succ_le (fifthRootFloor x)
  rw [correctionCount, correctionCount]
  have hmono : primePowerCount (fifthRootFloor (x + 1)) ≤
      primePowerCount (fifthRootFloor x + 1) := by
    rw [primePowerCount]
    exact Finset.card_le_card (by
      intro q hq
      simp only [Finset.mem_filter, Finset.mem_Icc] at hq ⊢
      exact ⟨⟨hq.1.1, hq.1.2.trans hr⟩, hq.2⟩)
  omega

lemma primePowerCount_eq_piStar (y : ℕ) :
    primePowerCount y = PrimePowers.piStar y := by
  unfold primePowerCount PrimePowers.piStar PrimePowers.primePowersUpTo
  apply congrArg Finset.card
  ext q
  simp only [mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨hq1, hqy⟩, hq⟩
    exact ⟨⟨hq.one_lt, hqy⟩, hq⟩
  · rintro ⟨⟨hq2, hqy⟩, hq⟩
    exact ⟨⟨(by omega), hqy⟩, hq⟩

lemma correctionCount_eq_two_mul_piStar (y : ℕ) :
    correctionCount y = 2 * PrimePowers.piStar y := by
  simp [correctionCount, primePowerCount_eq_piStar]

lemma approximationCertificate_residual_den_eq
    {r : ℚ} {x R : ℕ} (C : ApproximationCertificate r x R) :
    C.residual.den = C.denominator := by
  have hb : (0 : ℤ) < C.denominator := by exact_mod_cast C.denominator_pos
  have hcoprime : Nat.Coprime
      ((C.numerator : ℤ).natAbs) ((C.denominator : ℤ).natAbs) := by
    simpa using C.reduced
  have hden := Rat.den_div_eq_of_coprime hb hcoprime
  change (((C.numerator : ℚ) / C.denominator).den : ℤ) =
    (C.denominator : ℤ) at hden
  exact_mod_cast hden

lemma approximationCertificate_residual_largestPart_le
    {r : ℚ} {x R : ℕ} (C : ApproximationCertificate r x R) :
    PrimePowers.largestPrimePowerPart C.residual.den ≤ fifthRootFloor x := by
  rw [approximationCertificate_residual_den_eq C,
    PrimePowers.largestPrimePowerPart_le_iff]
  intro q hq
  have hqdata := (PrimePowers.mem_primePowerParts C.denominator_pos.ne').mp hq
  exact le_fifthRootFloor_of_pow_five_le
    (C.denominator_primePower_bound q hqdata.1 hqdata.2.1)

lemma approximationCertificate_residual_lt_one
    {r : ℚ} {x R : ℕ} (C : ApproximationCertificate r x R) :
    C.residual < 1 := by
  have hcast : (C.residual : ℝ) =
      (C.numerator : ℝ) / C.denominator := by
    simp [ApproximationCertificate.residual]
  have hu := C.residual_upper
  rw [← hcast] at hu
  exact_mod_cast hu

lemma densityCutoff_ratio_tendsto :
    Tendsto (fun t : ℕ ↦ (densityCutoff t : ℝ) / (t : ℝ)) atTop
      (nhds Analytic.densityConstant) := by
  have h := (tendsto_nat_ceil_mul_div_atTop
    (R := ℝ) Analytic.densityConstant_pos.le).comp
      tendsto_natCast_atTop_atTop
  simpa [densityCutoff, Function.comp_def] using h

lemma bufferedCutoff_ratio_tendsto {error : ℕ → ℝ}
    (herror : Tendsto error atTop (nhds 0)) :
    Tendsto (fun t : ℕ ↦ (bufferedCutoff error t : ℝ) / (t : ℝ)) atTop
      (nhds Analytic.densityConstant) := by
  let coefficient : ℕ → ℝ := fun t ↦ Analytic.densityConstant + error t
  let scale : ℕ → ℝ := fun t ↦ coefficient t * (t : ℝ)
  have hcoefficient : Tendsto coefficient atTop (nhds Analytic.densityConstant) := by
    simpa [coefficient] using tendsto_const_nhds.add herror
  have hscale : Tendsto scale atTop atTop := by
    have hmul := tendsto_natCast_atTop_atTop.atTop_mul_pos
      Analytic.densityConstant_pos hcoefficient
    apply hmul.congr'
    filter_upwards [] with t
    simp [scale, mul_comm]
  have hround : Tendsto (fun t : ℕ ↦ (⌈scale t⌉₊ : ℝ) / scale t)
      atTop (nhds 1) := tendsto_nat_ceil_div_atTop.comp hscale
  have hprod := hround.mul hcoefficient
  have hprod' : Tendsto
      (fun t : ℕ ↦ (⌈scale t⌉₊ : ℝ) / scale t * coefficient t)
      atTop (nhds Analytic.densityConstant) := by simpa using hprod
  apply hprod'.congr'
  filter_upwards [hscale.eventually (eventually_gt_atTop (0 : ℝ)),
    eventually_gt_atTop (0 : ℕ)] with t hscalePos ht
  have hscaleNe : scale t ≠ 0 := hscalePos.ne'
  have htNe : (t : ℝ) ≠ 0 := by positivity
  have hcoefficientNe : coefficient t ≠ 0 := by
    intro hzero
    simp [scale, hzero] at hscalePos
  dsimp [bufferedCutoff]
  change (⌈scale t⌉₊ : ℝ) / scale t * coefficient t =
    (⌈(coefficient t) * (t : ℝ)⌉₊ : ℝ) / (t : ℝ)
  rw [show scale t = coefficient t * (t : ℝ) by rfl]
  field_simp

lemma cutoffBufferConstant_gt_square :
    Analytic.densityConstant ^ 2 < cutoffBufferConstant := by
  simp [cutoffBufferConstant]

lemma martinMargin_tendsto_zero :
    Tendsto martinMargin atTop (nhds 0) := by
  exact tendsto_inv_atTop_zero.comp
    (Real.tendsto_sqrt_atTop.comp tendsto_log_coe_at_top)

lemma martinMargin_pos :
    ∀ᶠ t : ℕ in atTop, 0 < martinMargin t := by
  filter_upwards [eventually_ge_atTop 2] with t ht
  exact inv_pos.mpr (Real.sqrt_pos.2 (Real.log_pos (by exact_mod_cast (by omega : 1 < t))))

lemma martinMargin_mul_t_tendsto_atTop :
    Tendsto (fun t : ℕ ↦ martinMargin t * (t : ℝ)) atTop atTop := by
  have hsqrtTop : Tendsto (fun t : ℕ ↦ Real.sqrt (t : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  apply tendsto_atTop.2
  intro b
  filter_upwards [hsqrtTop.eventually (eventually_ge_atTop b),
    eventually_ge_atTop 2] with t hbt ht
  apply hbt.trans
  have htR : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  have hlogPos : 0 < Real.log (t : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < t))
  have hlogLe : Real.log (t : ℝ) ≤ (t : ℝ) :=
    (Real.log_le_sub_one_of_pos htR).trans (by linarith)
  have hsqrtLe : Real.sqrt (Real.log (t : ℝ)) ≤ Real.sqrt (t : ℝ) :=
    Real.sqrt_le_sqrt hlogLe
  rw [martinMargin, inv_mul_eq_div, le_div_iff₀ (Real.sqrt_pos.2 hlogPos)]
  calc
    Real.sqrt (t : ℝ) * Real.sqrt (Real.log (t : ℝ)) ≤
        Real.sqrt (t : ℝ) * Real.sqrt (t : ℝ) := by
      exact mul_le_mul_of_nonneg_left hsqrtLe (Real.sqrt_nonneg _)
    _ = (t : ℝ) := Real.mul_self_sqrt htR.le

lemma martinLowerRatio_tendsto :
    Tendsto martinLowerRatio atTop (nhds (Real.exp (-1))) := by
  change Tendsto (fun t : ℕ ↦ Real.exp (-1) + martinMargin t) atTop
    (nhds (Real.exp (-1)))
  simpa using tendsto_const_nhds.add martinMargin_tendsto_zero

lemma eventually_martinLowerRatio_bounds :
    ∀ᶠ t : ℕ in atTop,
      Real.exp (-1) < martinLowerRatio t ∧ martinLowerRatio t < 1 := by
  have hexp : Real.exp (-1) < 1 := by
    rw [Real.exp_lt_one_iff]
    norm_num
  have hup := martinLowerRatio_tendsto.eventually
    (Iio_mem_nhds hexp)
  filter_upwards [martinMargin_pos, hup] with t hmargin halpha
  exact ⟨by simp [martinLowerRatio, hmargin], halpha⟩

lemma martinCutoff_ratio_tendsto :
    Tendsto (fun t : ℕ ↦ (martinCutoff t : ℝ) / (t : ℝ)) atTop
      (nhds Analytic.densityConstant) := by
  apply bufferedCutoff_ratio_tendsto
  simpa using martinMargin_tendsto_zero.const_mul cutoffBufferConstant

lemma martinLowerEndpoint_floor_ratio_tendsto :
    Tendsto
      (fun x : ℕ ↦
        ((⌊martinLowerRatio x * (x : ℝ)⌋₊ : ℕ) : ℝ) / (x : ℝ))
      atTop (nhds (Real.exp (-1))) := by
  let scale : ℕ → ℝ := fun x ↦ martinLowerRatio x * (x : ℝ)
  have haPos : 0 < Real.exp (-1) := Real.exp_pos _
  have hscale : Tendsto scale atTop atTop := by
    have hmul := tendsto_natCast_atTop_atTop.atTop_mul_pos haPos
      martinLowerRatio_tendsto
    apply hmul.congr'
    filter_upwards [] with x
    simp [scale, mul_comm]
  have hround : Tendsto
      (fun x : ℕ ↦ ((⌊scale x⌋₊ : ℕ) : ℝ) / scale x)
      atTop (nhds 1) := tendsto_nat_floor_div_atTop.comp hscale
  have hprod := hround.mul martinLowerRatio_tendsto
  have hprod' : Tendsto
      (fun x : ℕ ↦ ((⌊scale x⌋₊ : ℕ) : ℝ) / scale x * martinLowerRatio x)
      atTop (nhds (Real.exp (-1))) := by simpa using hprod
  apply hprod'.congr'
  filter_upwards [hscale.eventually (eventually_gt_atTop (0 : ℝ)),
    eventually_gt_atTop (0 : ℕ)] with x hscalePos hx
  have hxne : (x : ℝ) ≠ 0 := by positivity
  have hane : martinLowerRatio x ≠ 0 := by
    intro ha
    simp [scale, ha] at hscalePos
  dsimp [scale]
  field_simp

lemma movingFullInitialInterval_card_ratio_tendsto :
    Tendsto
      (fun x : ℕ ↦
        ((fullInitialIntervalAt (martinLowerRatio x) x).card : ℝ) / (x : ℝ))
      atTop (nhds (1 - Real.exp (-1))) := by
  have hlim := (tendsto_const_nhds :
    Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1)).sub
      martinLowerEndpoint_floor_ratio_tendsto
  apply hlim.congr'
  filter_upwards [eventually_martinLowerRatio_bounds,
    eventually_ge_atTop 1] with x halpha hx
  have hfloorle : ⌊martinLowerRatio x * (x : ℝ)⌋₊ ≤ x := by
    have hreal : ((⌊martinLowerRatio x * (x : ℝ)⌋₊ : ℕ) : ℝ) ≤ (x : ℝ) :=
      (Nat.floor_le (mul_nonneg
        ((Real.exp_pos (-1)).trans halpha.1).le
        (Nat.cast_nonneg x))).trans
        (mul_le_of_le_one_left (Nat.cast_nonneg x) halpha.2.le)
    exact_mod_cast hreal
  rw [show (fullInitialIntervalAt (martinLowerRatio x) x).card =
      x - ⌊martinLowerRatio x * (x : ℝ)⌋₊ by
    simp [fullInitialIntervalAt], Nat.cast_sub hfloorle]
  field_simp

lemma movingInitialRoughPart_card_ratio_tendsto_zero :
    Tendsto
      (fun x : ℕ ↦
        ((initialRoughPartAt (martinLowerRatio x) x).card : ℝ) / (x : ℝ))
      atTop (nhds 0) := by
  have hglobal :=
    (RoughCounts.roughNumbersIn_logPowerCutoff_card_isLittleO 30).tendsto_div_nhds_zero
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun x ↦
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards with x
    have hc : ((initialRoughPartAt (martinLowerRatio x) x).card : ℝ) ≤
        ((RoughCounts.roughNumbersIn 1 x
          (RoughCounts.logPowerCutoff 30 x)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card
        (initialRoughPartAt_subset_global (martinLowerRatio x) x)
    exact div_le_div_of_nonneg_right hc (Nat.cast_nonneg x)
  · exact hglobal

/-- Quantitative form of the rough-cardinality estimate.  The discarded
prime-power-rough terms are negligible even relative to the moving
`x / sqrt(log x)` surplus. -/
lemma globalRoughPart_div_marginScale_tendsto_zero :
    Tendsto
      (fun x : ℕ ↦
        ((RoughCounts.roughNumbersIn 1 x
          (RoughCounts.logPowerCutoff 30 x)).card : ℝ) /
          ((x : ℝ) * martinMargin x)) atTop (nhds 0) := by
  have htail :=
    RoughCounts.primePowerReciprocalTail_logPowerCutoff_mul_sqrt_tendsto_zero 30
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop 2] with x hx
    exact div_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (Nat.cast_nonneg x)
        (inv_nonneg.mpr (Real.sqrt_nonneg _)))
  · filter_upwards [eventually_ge_atTop 2] with x hx
    have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
    have hlogpos : 0 < Real.log (x : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < x))
    have hsqrtpos : 0 < Real.sqrt (Real.log (x : ℝ)) :=
      Real.sqrt_pos.2 hlogpos
    have hmarginpos : 0 < martinMargin x := by
      rw [martinMargin]
      positivity
    have hc := RoughCounts.roughNumbersIn_card_le_mul_tail
      1 x (RoughCounts.logPowerCutoff 30 x)
    calc
      ((RoughCounts.roughNumbersIn 1 x
          (RoughCounts.logPowerCutoff 30 x)).card : ℝ) /
          ((x : ℝ) * martinMargin x) ≤
          ((x : ℝ) * RoughCounts.primePowerReciprocalTail x
            (RoughCounts.logPowerCutoff 30 x)) /
              ((x : ℝ) * martinMargin x) := by
        exact div_le_div_of_nonneg_right hc
          (mul_nonneg hxpos.le hmarginpos.le)
      _ = RoughCounts.primePowerReciprocalTail x
            (RoughCounts.logPowerCutoff 30 x) *
          Real.sqrt (Real.log (x : ℝ)) := by
        rw [martinMargin]
        field_simp [hxpos.ne', hsqrtpos.ne']
  · exact htail

lemma movingInitialRoughPart_div_marginScale_tendsto_zero :
    Tendsto
      (fun x : ℕ ↦
        ((initialRoughPartAt (martinLowerRatio x) x).card : ℝ) /
          ((x : ℝ) * martinMargin x)) atTop (nhds 0) := by
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop 2] with x hx
    exact div_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (Nat.cast_nonneg x)
        (inv_nonneg.mpr (Real.sqrt_nonneg _)))
  · filter_upwards [eventually_ge_atTop 2] with x hx
    have hmargin : 0 ≤ martinMargin x := by
      rw [martinMargin]
      positivity
    have hc : ((initialRoughPartAt (martinLowerRatio x) x).card : ℝ) ≤
        ((RoughCounts.roughNumbersIn 1 x
          (RoughCounts.logPowerCutoff 30 x)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card
        (initialRoughPartAt_subset_global (martinLowerRatio x) x)
    exact div_le_div_of_nonneg_right hc
      (mul_nonneg (Nat.cast_nonneg x) hmargin)
  · exact globalRoughPart_div_marginScale_tendsto_zero

lemma martinInitialBlock_card_ratio_tendsto :
    Tendsto (fun x : ℕ ↦ ((martinInitialBlock x).card : ℝ) / (x : ℝ))
      atTop (nhds (1 - Real.exp (-1))) := by
  have hlim := movingFullInitialInterval_card_ratio_tendsto.sub
    movingInitialRoughPart_card_ratio_tendsto_zero
  have hlim' : Tendsto
      (fun x : ℕ ↦
        ((fullInitialIntervalAt (martinLowerRatio x) x).card : ℝ) / x -
          ((initialRoughPartAt (martinLowerRatio x) x).card : ℝ) / x)
      atTop (nhds (1 - Real.exp (-1))) := by simpa using hlim
  apply hlim'.congr'
  filter_upwards with x
  have hsub := initialRoughPartAt_subset_full (martinLowerRatio x) x
  rw [martinInitialBlock, initialBlockAt_eq_sdiff,
    Finset.card_sdiff_of_subset hsub,
    Nat.cast_sub (Finset.card_le_card hsub)]
  ring

/-! ## Fifth-root asymptotics for an arbitrary asymptotically optimal cutoff -/

lemma fifthRoot_ratio_formula {x t : ℕ} (ht : 0 < t) :
    ((x : ℝ) ^ ((5 : ℝ)⁻¹)) / t =
      (((x : ℝ) / t) ^ ((5 : ℝ)⁻¹)) *
        (t : ℝ) ^ (-(4 / 5 : ℝ)) := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  calc
    ((x : ℝ) ^ ((5 : ℝ)⁻¹)) / t =
        ((((x : ℝ) / t) * t) ^ ((5 : ℝ)⁻¹)) / t := by
          rw [div_mul_cancel₀ _ htR.ne']
    _ = ((((x : ℝ) / t) ^ ((5 : ℝ)⁻¹)) *
          (t : ℝ) ^ ((5 : ℝ)⁻¹)) / t := by
          rw [Real.mul_rpow (by positivity) htR.le]
    _ = (((x : ℝ) / t) ^ ((5 : ℝ)⁻¹)) *
          (t : ℝ) ^ (-(4 / 5 : ℝ)) := by
          have hquot : (t : ℝ) ^ ((5 : ℝ)⁻¹) / t =
              (t : ℝ) ^ (-(4 / 5 : ℝ)) := by
            conv_lhs => rhs; rw [← Real.rpow_one (t : ℝ)]
            rw [← Real.rpow_sub htR]
            congr 1
            norm_num
          rw [mul_div_assoc, hquot]

lemma natCast_cutoff_tendsto_atTop
    {x : ℕ → ℕ} {C : ℝ} (hC : 0 < C)
    (hx : Tendsto (fun t : ℕ ↦ (x t : ℝ) / (t : ℝ)) atTop (nhds C)) :
    Tendsto (fun t : ℕ ↦ (x t : ℝ)) atTop atTop := by
  have hprod : Tendsto
      (fun t : ℕ ↦ (t : ℝ) * ((x t : ℝ) / (t : ℝ)))
      atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_pos hC hx
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with t ht
  have htR : (t : ℝ) ≠ 0 := by positivity
  field_simp

lemma fifthRootFloor_tendsto_atTop
    {x : ℕ → ℕ} {C : ℝ} (hC : 0 < C)
    (hx : Tendsto (fun t : ℕ ↦ (x t : ℝ) / (t : ℝ)) atTop (nhds C)) :
    Tendsto (fun t ↦ fifthRootFloor (x t)) atTop atTop := by
  apply tendsto_nat_floor_atTop.comp
  apply (tendsto_rpow_atTop (by positivity : (0 : ℝ) < (5 : ℝ)⁻¹)).comp
  exact natCast_cutoff_tendsto_atTop hC hx

lemma fifthRootFloor_log_tendsto_atTop
    {x : ℕ → ℕ} {C : ℝ} (hC : 0 < C)
    (hx : Tendsto (fun t : ℕ ↦ (x t : ℝ) / (t : ℝ)) atTop (nhds C)) :
    Tendsto (fun t : ℕ ↦ Real.log (fifthRootFloor (x t) : ℝ)) atTop atTop := by
  exact tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.comp (fifthRootFloor_tendsto_atTop hC hx))

lemma fifthRootFloor_inv_log_tendsto_zero
    {x : ℕ → ℕ} {C : ℝ} (hC : 0 < C)
    (hx : Tendsto (fun t : ℕ ↦ (x t : ℝ) / (t : ℝ)) atTop (nhds C)) :
    Tendsto (fun t : ℕ ↦ (Real.log (fifthRootFloor (x t) : ℝ))⁻¹)
      atTop (nhds 0) := by
  exact (fifthRootFloor_log_tendsto_atTop hC hx).inv_tendsto_atTop

lemma fifthRootFloor_ratio_tendsto_zero
    {x : ℕ → ℕ} {C : ℝ} (hC : 0 < C)
    (hx : Tendsto (fun t : ℕ ↦ (x t : ℝ) / (t : ℝ)) atTop (nhds C)) :
    Tendsto (fun t : ℕ ↦ (fifthRootFloor (x t) : ℝ) / (t : ℝ))
      atTop (nhds 0) := by
  have hfirst : Tendsto
      (fun t : ℕ ↦ ((x t : ℝ) / (t : ℝ)) ^ ((5 : ℝ)⁻¹))
      atTop (nhds (C ^ ((5 : ℝ)⁻¹))) :=
    hx.rpow_const (.inl hC.ne')
  have hsecond : Tendsto (fun t : ℕ ↦ (t : ℝ) ^ (-(4 / 5 : ℝ)))
      atTop (nhds 0) := by
    exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 4 / 5)).comp
      tendsto_natCast_atTop_atTop
  have hroot : Tendsto
      (fun t : ℕ ↦ ((x t : ℝ) ^ ((5 : ℝ)⁻¹)) / (t : ℝ))
      atTop (nhds 0) := by
    have hm := hfirst.mul hsecond
    have heq : (fun t : ℕ ↦
        ((x t : ℝ) / (t : ℝ)) ^ ((5 : ℝ)⁻¹) *
          (t : ℝ) ^ (-(4 / 5 : ℝ))) =ᶠ[atTop]
        (fun t : ℕ ↦ ((x t : ℝ) ^ ((5 : ℝ)⁻¹)) / (t : ℝ)) := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with t ht
      exact (fifthRoot_ratio_formula ht).symm
    simpa only [mul_zero] using hm.congr' heq
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hroot
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with t ht
    positivity
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with t ht
    exact div_le_div_of_nonneg_right (fifthRootFloor_cast_le (x t)) (by positivity)

lemma correctionCount_ratio_tendsto_zero
    {x : ℕ → ℕ} {C : ℝ} (hC : 0 < C)
    (hx : Tendsto (fun t : ℕ ↦ (x t : ℝ) / (t : ℝ)) atTop (nhds C)) :
    Tendsto
      (fun t : ℕ ↦
        (correctionCount (fifthRootFloor (x t)) : ℝ) / (t : ℝ))
      atTop (nhds 0) := by
  have hy := fifthRootFloor_ratio_tendsto_zero hC hx
  have hupper : Tendsto
      (fun t : ℕ ↦ 2 * ((fifthRootFloor (x t) : ℝ) / (t : ℝ)))
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hy
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with t ht
    positivity
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with t ht
    have hc : (correctionCount (fifthRootFloor (x t)) : ℝ) ≤
        (2 * fifthRootFloor (x t) : ℕ) := by
      exact_mod_cast correctionCount_le_twice (fifthRootFloor (x t))
    calc
      (correctionCount (fifthRootFloor (x t)) : ℝ) / t ≤
          (2 * fifthRootFloor (x t) : ℕ) / (t : ℝ) :=
        div_le_div_of_nonneg_right hc (by positivity)
      _ = 2 * ((fifthRootFloor (x t) : ℝ) / (t : ℝ)) := by
        push_cast
        ring

lemma correctionCount_isLittleO
    {x : ℕ → ℕ} {C : ℝ} (hC : 0 < C)
    (hx : Tendsto (fun t : ℕ ↦ (x t : ℝ) / (t : ℝ)) atTop (nhds C)) :
    (fun t : ℕ ↦ (correctionCount (fifthRootFloor (x t)) : ℝ))
      =o[atTop] (fun t : ℕ ↦ (t : ℝ)) := by
  apply (Asymptotics.isLittleO_iff_tendsto' ?_).2
    (correctionCount_ratio_tendsto_zero hC hx)
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with t ht
  intro hzero
  have htR : (t : ℝ) ≠ 0 := by positivity
  exact (htR hzero).elim

lemma eventually_correctionCount_le
    {x : ℕ → ℕ} {C : ℝ} (hC : 0 < C)
    (hx : Tendsto (fun t : ℕ ↦ (x t : ℝ) / (t : ℝ)) atTop (nhds C)) :
    ∀ᶠ t in atTop, correctionCount (fifthRootFloor (x t)) ≤ t := by
  have hratio := correctionCount_ratio_tendsto_zero hC hx
  have hlt : ∀ᶠ t in atTop,
      (correctionCount (fifthRootFloor (x t)) : ℝ) / (t : ℝ) < 1 :=
    hratio.eventually (Iio_mem_nhds zero_lt_one)
  filter_upwards [hlt, eventually_gt_atTop (0 : ℕ)] with t hlt ht
  rw [div_lt_iff₀ (by exact_mod_cast ht : (0 : ℝ) < t)] at hlt
  have hcR : (correctionCount (fifthRootFloor (x t)) : ℝ) ≤ (t : ℝ) := by
    linarith
  exact_mod_cast hcR

lemma mainCount_ratio_tendsto_one
    {x : ℕ → ℕ} {C : ℝ} (hC : 0 < C)
    (hx : Tendsto (fun t : ℕ ↦ (x t : ℝ) / (t : ℝ)) atTop (nhds C)) :
    Tendsto
      (fun t : ℕ ↦ (mainCount t (fifthRootFloor (x t)) : ℝ) / (t : ℝ))
      atTop (nhds 1) := by
  have hcorr := correctionCount_ratio_tendsto_zero hC hx
  have hbase : Tendsto
      (fun t : ℕ ↦ 1 -
        (correctionCount (fifthRootFloor (x t)) : ℝ) / (t : ℝ))
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hcorr
  apply hbase.congr'
  filter_upwards [eventually_correctionCount_le hC hx,
    eventually_gt_atTop (0 : ℕ)] with t hle ht
  rw [mainCount, Nat.cast_sub hle]
  field_simp

/-! ## Separation of the main and correction denominator ranges -/

lemma correctionCutoff_le_of_two_le {x y : ℕ} (hy : 2 ≤ y)
    (hy5 : y ^ 5 ≤ x) : correctionCutoff y ≤ x := by
  apply le_trans ?_ hy5
  rw [correctionCutoff]
  calc
    2 * y ^ 4 ≤ y * y ^ 4 := Nat.mul_le_mul_right (y ^ 4) hy
    _ = y ^ 5 := by ring

lemma correctionCutoff_lt_largeLowerCutoff {x y : ℕ}
    (hy : separationThreshold ≤ y) (hy5 : y ^ 5 ≤ x) :
    correctionCutoff y < largeLowerCutoff x := by
  have hy2 : 2 ≤ y := (le_max_left 2 ⌈6 * Real.exp 1⌉₊).trans hy
  have hyceil : ⌈6 * Real.exp 1⌉₊ ≤ y :=
    (le_max_right 2 ⌈6 * Real.exp 1⌉₊).trans hy
  have hscale : 6 * Real.exp 1 ≤ (y : ℝ) :=
    (Nat.le_ceil (6 * Real.exp 1)).trans (by exact_mod_cast hyceil)
  have hexp : Real.exp (-1) * Real.exp 1 = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hmul : (6 : ℝ) ≤ Real.exp (-1) * y := by
    have := mul_le_mul_of_nonneg_left hscale (Real.exp_pos (-1)).le
    have heq : Real.exp (-1) * (6 * Real.exp 1) = (6 : ℝ) := by
      calc
        Real.exp (-1) * (6 * Real.exp 1) = 6 * (Real.exp (-1) * Real.exp 1) := by ring
        _ = 6 := by rw [hexp]; ring
    rw [heq] at this
    exact this
  have hy4pos : (1 : ℝ) ≤ (y : ℝ) ^ 4 := by
    have hy1 : (1 : ℝ) ≤ y := by exact_mod_cast (show 1 ≤ y by omega)
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hy1 4]
  have hcore : 3 * (y : ℝ) ^ 4 ≤
      Real.exp (-1) * (y : ℝ) ^ 5 / 2 := by
    have hmul' := mul_le_mul_of_nonneg_left hmul
      (show 0 ≤ (y : ℝ) ^ 4 / 2 by positivity)
    calc
      3 * (y : ℝ) ^ 4 = ((y : ℝ) ^ 4 / 2) * 6 := by ring
      _ ≤ ((y : ℝ) ^ 4 / 2) * (Real.exp (-1) * y) := hmul'
      _ = Real.exp (-1) * (y : ℝ) ^ 5 / 2 := by ring
  have hy5R : (y : ℝ) ^ 5 ≤ (x : ℝ) := by exact_mod_cast hy5
  have hreal : ((correctionCutoff y + 1 : ℕ) : ℝ) ≤
      Real.exp (-1) * (x : ℝ) / 2 := by
    rw [correctionCutoff]
    push_cast
    calc
      2 * (y : ℝ) ^ 4 + 1 ≤ 3 * (y : ℝ) ^ 4 := by linarith
      _ ≤ Real.exp (-1) * (y : ℝ) ^ 5 / 2 := hcore
      _ ≤ Real.exp (-1) * (x : ℝ) / 2 := by
        gcongr
  have hfloor : correctionCutoff y + 1 ≤ largeLowerCutoff x := by
    rw [largeLowerCutoff, Nat.le_floor_iff (by positivity)]
    exact hreal
  omega

/-- Flooring the fifth root costs less than one.  A deliberately coarse sixth
power absorbs that rounding once the root is at least `32`. -/
lemma cutoff_lt_sixth_power_fifthRoot {x : ℕ} (hy : 32 ≤ fifthRootFloor x) :
    x < fifthRootFloor x ^ 6 := by
  let y := fifthRootFloor x
  have hroot : (x : ℝ) ^ ((5 : ℝ)⁻¹) < (y + 1 : ℕ) := by
    rw [Nat.cast_add, Nat.cast_one]
    dsimp only [y, fifthRootFloor]
    exact Nat.lt_floor_add_one ((x : ℝ) ^ ((5 : ℝ)⁻¹))
  have hpowR := pow_lt_pow_left₀ hroot
    (Real.rpow_nonneg (Nat.cast_nonneg x) _) (by norm_num : (5 : ℕ) ≠ 0)
  have hrootPow : ((x : ℝ) ^ ((5 : ℝ)⁻¹)) ^ 5 = (x : ℝ) := by
    convert Real.rpow_inv_natCast_pow (Nat.cast_nonneg x)
      (by norm_num : (5 : ℕ) ≠ 0) using 1
    all_goals norm_num
  rw [hrootPow] at hpowR
  have hxSuccPow : x < (y + 1) ^ 5 := by exact_mod_cast hpowR
  have hsucc : y + 1 ≤ 2 * y := by dsimp [y] at hy ⊢; omega
  have hsuccPow : (y + 1) ^ 5 ≤ (2 * y) ^ 5 :=
    pow_le_pow_left₀ (Nat.zero_le _) hsucc 5
  have h32 : 32 * y ^ 5 ≤ y * y ^ 5 :=
    Nat.mul_le_mul_right (y ^ 5) (by simpa [y] using hy)
  calc
    x < (y + 1) ^ 5 := hxSuccPow
    _ ≤ (2 * y) ^ 5 := hsuccPow
    _ = 32 * y ^ 5 := by ring
    _ ≤ y * y ^ 5 := h32
    _ = y ^ 6 := by ring

lemma log_cutoff_lt_six_mul_log_fifthRoot {x : ℕ}
    (hy : 32 ≤ fifthRootFloor x) :
    Real.log (x : ℝ) < 6 * Real.log (fifthRootFloor x : ℝ) := by
  have hxy := cutoff_lt_sixth_power_fifthRoot hy
  have hxpos : (0 : ℝ) < x := by
    have hy5 := fifthRootFloor_pow_five_le x
    exact_mod_cast (lt_of_lt_of_le (by positivity : 0 < fifthRootFloor x ^ 5) hy5)
  have hypowpos : (0 : ℝ) < fifthRootFloor x ^ 6 := by positivity
  have hlog := Real.strictMonoOn_log hxpos hypowpos (by exact_mod_cast hxy)
  simpa [Real.log_pow] using hlog

lemma one_sixth_mul_inv_log_fifthRoot_lt_inv_log_cutoff {x : ℕ}
    (hy : 32 ≤ fifthRootFloor x) :
    (1 / 6 : ℝ) * (Real.log (fifthRootFloor x : ℝ))⁻¹ <
      (Real.log (x : ℝ))⁻¹ := by
  have hyone : (1 : ℝ) < fifthRootFloor x := by exact_mod_cast (show 1 < fifthRootFloor x by omega)
  have hylog : 0 < Real.log (fifthRootFloor x : ℝ) := Real.log_pos hyone
  have hxone : (1 : ℝ) < x := by
    have hy5 := fifthRootFloor_pow_five_le x
    have : 1 < fifthRootFloor x ^ 5 :=
      one_lt_pow₀ (show 1 < fifthRootFloor x by omega) (by norm_num)
    exact_mod_cast this.trans_le hy5
  have hxlog : 0 < Real.log (x : ℝ) := Real.log_pos hxone
  have hlog := log_cutoff_lt_six_mul_log_fifthRoot hy
  have hinv := one_div_lt_one_div_of_lt hxlog hlog
  calc
    (1 / 6 : ℝ) * (Real.log (fifthRootFloor x : ℝ))⁻¹ =
        1 / (6 * Real.log (fifthRootFloor x : ℝ)) := by field_simp
    _ < 1 / Real.log (x : ℝ) := hinv
    _ = (Real.log (x : ℝ))⁻¹ := one_div _

/-- Proposition 6's lower residual bound at scale `x` implies the weakened
fixed-constant bound required by Proposition 7 at the rounded fifth-root
scale.  The slack from `1/5` to `1/6` absorbs the floor. -/
lemma approximationCertificate_residual_lower_one_sixth
    {x R : ℕ} (C : ApproximationCertificate (1 : ℚ) x R)
    (hy : 32 ≤ fifthRootFloor x) :
    (1 / 6 : ℝ) * (Real.log (fifthRootFloor x : ℝ))⁻¹ <
      (C.residual : ℝ) := by
  have hcast : (C.residual : ℝ) =
      (C.numerator : ℝ) / (C.denominator : ℝ) := by
    simp [ApproximationCertificate.residual]
  rw [hcast]
  exact (one_sixth_mul_inv_log_fifthRoot_lt_inv_log_cutoff hy).trans
    C.residual_lower

lemma eventually_cutoffs_separated
    {x : ℕ → ℕ} {C : ℝ} (hC : 0 < C)
    (hx : Tendsto (fun t : ℕ ↦ (x t : ℝ) / (t : ℝ)) atTop (nhds C)) :
    ∀ᶠ t in atTop,
      correctionCutoff (fifthRootFloor (x t)) < largeLowerCutoff (x t) := by
  have hyTop := fifthRootFloor_tendsto_atTop hC hx
  filter_upwards [hyTop.eventually_ge_atTop separationThreshold] with t ht
  exact correctionCutoff_lt_largeLowerCutoff ht
    (fifthRootFloor_pow_five_le (x t))

lemma eventually_correctionCutoff_le
    {x : ℕ → ℕ} {C : ℝ} (hC : 0 < C)
    (hx : Tendsto (fun t : ℕ ↦ (x t : ℝ) / (t : ℝ)) atTop (nhds C)) :
    ∀ᶠ t in atTop, correctionCutoff (fifthRootFloor (x t)) ≤ x t := by
  have hyTop := fifthRootFloor_tendsto_atTop hC hx
  filter_upwards [hyTop.eventually_ge_atTop 2] with t ht
  exact correctionCutoff_le_of_two_le ht (fifthRootFloor_pow_five_le (x t))

/-! ## The concrete moving parameters -/

lemma identity_cutoff_ratio_tendsto :
    Tendsto (fun x : ℕ ↦ (x : ℝ) / (x : ℝ)) atTop (nhds 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with x hx
  field_simp

lemma martinScore_ratio_tendsto :
    Tendsto (fun x : ℕ ↦ (martinScore x : ℝ) / (x : ℝ)) atTop
      (nhds (1 - Real.exp (-1))) := by
  have hcorr := correctionCount_ratio_tendsto_zero (C := (1 : ℝ))
    (by norm_num) identity_cutoff_ratio_tendsto
  have hsum := martinInitialBlock_card_ratio_tendsto.add hcorr
  have hsum' : Tendsto
      (fun x : ℕ ↦ ((martinInitialBlock x).card : ℝ) / x +
        (correctionCount (fifthRootFloor x) : ℝ) / x)
      atTop (nhds (1 - Real.exp (-1))) := by simpa using hsum
  apply hsum'.congr'
  filter_upwards with x
  simp only [martinScore, Nat.cast_add]
  ring

lemma martinScore_tendsto_atTop :
    Tendsto martinScore atTop atTop := by
  have hd : 0 < 1 - Real.exp (-1) := by
    rw [sub_pos, Real.exp_lt_one_iff]
    norm_num
  have hreal := natCast_cutoff_tendsto_atTop hd martinScore_ratio_tendsto
  exact tendsto_natCast_atTop_iff.mp hreal

lemma martinCutoff_tendsto_atTop :
    Tendsto martinCutoff atTop atTop := by
  have hreal := natCast_cutoff_tendsto_atTop Analytic.densityConstant_pos
    martinCutoff_ratio_tendsto
  exact tendsto_natCast_atTop_iff.mp hreal

lemma martinCorrectionScale_tendsto_atTop :
    Tendsto martinCorrectionScale atTop atTop := by
  exact fifthRootFloor_tendsto_atTop Analytic.densityConstant_pos
    martinCutoff_ratio_tendsto

lemma martinCorrectionCount_ratio_tendsto_zero :
    Tendsto
      (fun t : ℕ ↦ (correctionCount (martinCorrectionScale t) : ℝ) / (t : ℝ))
      atTop (nhds 0) := by
  exact correctionCount_ratio_tendsto_zero Analytic.densityConstant_pos
    martinCutoff_ratio_tendsto

lemma martinCorrectionCount_isLittleO :
    (fun t : ℕ ↦ (correctionCount (martinCorrectionScale t) : ℝ))
      =o[atTop] (fun t : ℕ ↦ (t : ℝ)) := by
  exact correctionCount_isLittleO Analytic.densityConstant_pos
    martinCutoff_ratio_tendsto

lemma eventually_martinCorrectionCount_le :
    ∀ᶠ t : ℕ in atTop, correctionCount (martinCorrectionScale t) ≤ t := by
  exact eventually_correctionCount_le Analytic.densityConstant_pos
    martinCutoff_ratio_tendsto

lemma martinMainCount_ratio_tendsto_one :
    Tendsto (fun t : ℕ ↦ (martinMainCount t : ℝ) / (t : ℝ))
      atTop (nhds 1) := by
  exact mainCount_ratio_tendsto_one Analytic.densityConstant_pos
    martinCutoff_ratio_tendsto

lemma eventually_martinCutoffs_separated :
    ∀ᶠ t : ℕ in atTop,
      correctionCutoff (martinCorrectionScale t) <
        largeLowerCutoff (martinCutoff t) := by
  exact eventually_cutoffs_separated Analytic.densityConstant_pos
    martinCutoff_ratio_tendsto

lemma eventually_martinCorrectionCutoff_le :
    ∀ᶠ t : ℕ in atTop,
      correctionCutoff (martinCorrectionScale t) ≤ martinCutoff t := by
  exact eventually_correctionCutoff_le Analytic.densityConstant_pos
    martinCutoff_ratio_tendsto

/-! ## Conversion of Propositions 6 and 7 into the assembly input -/

theorem propositionFourInput_of_certificates
    {t x y R : ℕ} (C : ApproximationCertificate (1 : ℚ) x R)
    {correction : Finset ℕ}
    (hR : R = mainCount t y)
    (hcount : correctionCount y ≤ t)
    (hcorrectionCard : correction.card = correctionCount y)
    (hcorrectionZero : 0 ∉ correction)
    (hcorrectionSum : UnitFractions.rec_sum correction = C.residual)
    (hcorrectionUpper : ∀ n ∈ correction, n ≤ correctionCutoff y)
    (hseparated : correctionCutoff y < largeLowerCutoff x)
    (hcorrectionCutoff : correctionCutoff y ≤ x) :
    PropositionFourInput 1 t y R (largeLowerCutoff x) x (C.residual : ℝ)
      C.denominators correction := by
  refine
    { R_eq := hR
      correctionCount_le := hcount
      large_card := C.card_eq
      correction_card := hcorrectionCard
      large_zero_not_mem := C.zero_not_mem
      correction_zero_not_mem := hcorrectionZero
      large_sum := ?_
      correction_sum := ?_
      large_lower := ?_
      large_upper := ?_
      correction_upper := hcorrectionUpper
      cutoffs_separated := hseparated
      correctionCutoff_le := hcorrectionCutoff }
  · rw [show reciprocalSum C.denominators = realRecSum C.denominators by rfl,
      realRecSum_eq_ratCast, C.reciprocal_sum_eq_sub_residual]
    norm_num
  · rw [show reciprocalSum correction = realRecSum correction by rfl,
      realRecSum_eq_ratCast, hcorrectionSum]
  · intro n hn
    have hfloorR : (largeLowerCutoff x : ℝ) ≤
        Real.exp (-1) * (x : ℝ) / 2 := by
      exact Nat.floor_le (by positivity)
    have hnR : Real.exp (-1) * (x : ℝ) / 2 ≤ (n : ℝ) := by
      simpa using (C.interval n hn).1
    exact_mod_cast hfloorR.trans hnR
  · intro n hn
    exact_mod_cast (C.interval n hn).2

/-- The same bridge with Proposition 7's native cardinality notation
`2 * piStar y`. -/
theorem propositionFourInput_of_martin_certificates
    {t x y R : ℕ} (C : ApproximationCertificate (1 : ℚ) x R)
    {correction : Finset ℕ}
    (hR : R = mainCount t y)
    (hcount : correctionCount y ≤ t)
    (hcorrectionCard : correction.card = 2 * PrimePowers.piStar y)
    (hcorrectionZero : 0 ∉ correction)
    (hcorrectionSum : UnitFractions.rec_sum correction = C.residual)
    (hcorrectionUpper : ∀ n ∈ correction, n ≤ 2 * y ^ 4)
    (hseparated : correctionCutoff y < largeLowerCutoff x)
    (hcorrectionCutoff : correctionCutoff y ≤ x) :
    PropositionFourInput 1 t y R (largeLowerCutoff x) x (C.residual : ℝ)
      C.denominators correction := by
  apply propositionFourInput_of_certificates C hR hcount
  · simpa [correctionCount_eq_two_mul_piStar] using hcorrectionCard
  · exact hcorrectionZero
  · exact hcorrectionSum
  · simpa only [correctionCutoff] using hcorrectionUpper
  · exact hseparated
  · exact hcorrectionCutoff

/-- Proposition 7 turns every sufficiently large Proposition 6 certificate
at the rounded fifth-root scale into the complete finite assembly input.  This
is the unconditional Proposition 6-to-7 bridge: no arithmetic construction is
passed as a theorem argument. -/
theorem eventually_propositionFourInput_of_approximationCertificates
    {x : ℕ → ℕ} {C : ℝ} (hC : 0 < C)
    (hx : Tendsto (fun t : ℕ ↦ (x t : ℝ) / (t : ℝ)) atTop (nhds C))
    (hcert : ∀ᶠ t : ℕ in atTop,
      Nonempty (ApproximationCertificate (1 : ℚ) (x t)
        (mainCount t (fifthRootFloor (x t))))) :
    ∀ᶠ t in atTop,
      ∃ residual : ℝ, ∃ large correction : Finset ℕ,
        PropositionFourInput 1 t (fifthRootFloor (x t))
          (mainCount t (fifthRootFloor (x t))) (largeLowerCutoff (x t))
          (x t) residual large correction := by
  have hyTop := fifthRootFloor_tendsto_atTop hC hx
  have hp7 := hyTop.eventually
    (Proposition7.eventually_proposition7 (c := (1 / 6 : ℝ)) (by positivity))
  have hy32 := hyTop.eventually (eventually_ge_atTop 32)
  have hcount := eventually_correctionCount_le hC hx
  have hsep := eventually_cutoffs_separated hC hx
  have hcut := eventually_correctionCutoff_le hC hx
  filter_upwards [hcert, hp7, hy32, hcount, hsep, hcut]
      with t htCert htP7 htY htCount htSep htCut
  rcases htCert with ⟨cert⟩
  have hpart := approximationCertificate_residual_largestPart_le cert
  have hlower := approximationCertificate_residual_lower_one_sixth cert htY
  have hupperQ := approximationCertificate_residual_lt_one cert
  have hupper : (cert.residual : ℝ) < 1 := by exact_mod_cast hupperQ
  obtain ⟨E, hEcard, hEsum, hEzero, hEupper⟩ :=
    htP7 cert.residual hpart (by simpa [div_eq_mul_inv] using hlower) hupper
  refine ⟨(cert.residual : ℝ), cert.denominators, E, ?_⟩
  exact propositionFourInput_of_martin_certificates cert rfl htCount
    hEcard hEzero hEsum hEupper htSep htCut

/-- The existential filter form used once the unconditional Proposition 6 and
Proposition 7 constructions have supplied their certificates. -/
theorem eventually_upperWitness_of_eventually_input
    (x : ℕ → ℕ)
    (hinput : ∀ᶠ t in atTop,
      ∃ residual : ℝ, ∃ large correction : Finset ℕ,
        PropositionFourInput 1 t (fifthRootFloor (x t))
          (mainCount t (fifthRootFloor (x t))) (largeLowerCutoff (x t))
          (x t) residual large correction) :
    ∀ᶠ t in atTop, ∃ A : Finset ℕ, UpperWitness 1 t (x t) A := by
  filter_upwards [hinput] with t ht
  obtain ⟨residual, large, correction, hdata⟩ := ht
  exact ⟨large ∪ correction, hdata.assemble.2⟩

/-- Shift the term-count form of Proposition 4 to the `k + 1` convention of
the formal-conjectures statement. -/
theorem shift_to_formal_index
    (x : ℕ → ℕ)
    (hupper : ∀ᶠ t in atTop, ∃ A : Finset ℕ, UpperWitness 1 t (x t) A)
    (hx : Tendsto (fun t : ℕ ↦ (x t : ℝ) / (t : ℝ)) atTop
      (nhds Analytic.densityConstant)) :
    (∀ᶠ k in atTop,
      ∃ A : Finset ℕ, UpperWitness 1 k.succ (indexedCutoff x k) A) ∧
    Tendsto
      (fun k : ℕ ↦ (indexedCutoff x k : ℝ) / (k + 1 : ℕ)) atTop
      (nhds Analytic.densityConstant) := by
  have hshift := tendsto_add_atTop_nat 1
  constructor
  · have hpull := hshift.eventually hupper
    simpa [indexedCutoff, Nat.succ_eq_add_one, Function.comp_def] using hpull
  · have hpull := hx.comp hshift
    simpa [indexedCutoff, Nat.succ_eq_add_one, Function.comp_def] using hpull

/-- Complete high-level assembly, still phrased in terms of the eventual
certificate proposition that the arithmetic files discharge. -/
theorem propositionFour_from_eventually_input
    (x : ℕ → ℕ)
    (hx : Tendsto (fun t : ℕ ↦ (x t : ℝ) / (t : ℝ)) atTop
      (nhds Analytic.densityConstant))
    (hinput : ∀ᶠ t in atTop,
      ∃ residual : ℝ, ∃ large correction : Finset ℕ,
        PropositionFourInput 1 t (fifthRootFloor (x t))
          (mainCount t (fifthRootFloor (x t))) (largeLowerCutoff (x t))
          (x t) residual large correction) :
    (∀ᶠ k in atTop,
      ∃ A : Finset ℕ, UpperWitness 1 k.succ (indexedCutoff x k) A) ∧
    Tendsto
      (fun k : ℕ ↦ (indexedCutoff x k : ℝ) / (k + 1 : ℕ)) atTop
      (nhds Analytic.densityConstant) := by
  exact shift_to_formal_index x
    (eventually_upperWitness_of_eventually_input x hinput) hx

/-- Complete Proposition 4 once the concrete Proposition 6 certificate stream
has been constructed.  Proposition 7 is invoked internally by
`eventually_propositionFourInput_of_approximationCertificates`. -/
theorem propositionFour_of_approximationCertificates
    (x : ℕ → ℕ)
    (hx : Tendsto (fun t : ℕ ↦ (x t : ℝ) / (t : ℝ)) atTop
      (nhds Analytic.densityConstant))
    (hcert : ∀ᶠ t : ℕ in atTop,
      Nonempty (ApproximationCertificate (1 : ℚ) (x t)
        (mainCount t (fifthRootFloor (x t))))) :
    (∀ᶠ k in atTop,
      ∃ A : Finset ℕ, UpperWitness 1 k.succ (indexedCutoff x k) A) ∧
    Tendsto
      (fun k : ℕ ↦ (indexedCutoff x k : ℝ) / (k + 1 : ℕ)) atTop
      (nhds Analytic.densityConstant) := by
  apply propositionFour_from_eventually_input x hx
  exact eventually_propositionFourInput_of_approximationCertificates
    Analytic.densityConstant_pos hx hcert

end

end Erdos285.Proposition4

#print axioms Erdos285.Proposition4.fifthRootFloor_pow_five_le
#print axioms Erdos285.Proposition4.correctionCount_le_twice
#print axioms Erdos285.Proposition4.bufferedCutoff_ratio_tendsto
#print axioms Erdos285.Proposition4.correctionCount_isLittleO
#print axioms Erdos285.Proposition4.eventually_cutoffs_separated
#print axioms Erdos285.Proposition4.propositionFourInput_of_certificates
#print axioms Erdos285.Proposition4.eventually_upperWitness_of_eventually_input
#print axioms Erdos285.Proposition4.propositionFour_from_eventually_input
#print axioms Erdos285.Proposition4.propositionFour_of_approximationCertificates
