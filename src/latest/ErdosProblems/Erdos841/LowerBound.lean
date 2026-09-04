import ErdosProblems.Erdos841.Core

namespace Erdos841

lemma one_div_264_le_totallyRealDegreeEightUnitLogGap_div_eight :
    (1 / 264 : ℝ) ≤ totallyRealDegreeEightUnitLogGap / 8 := by
  have hlog : (2 / 33 : ℝ) ≤ Real.log (17 / 16 : ℝ) := by
    have h := Real.le_log_one_add_of_nonneg (show (0 : ℝ) ≤ 1 / 16 by norm_num)
    norm_num at h ⊢
    exact h
  rw [totallyRealDegreeEightUnitLogGap]
  nlinarith

lemma commonBoundedUnitLogBound_le_coarse
    (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (hdeg : Module.finrank ℚ K ≤ 8) {B : ℕ}
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B) :
    BoundedUnits.commonBoundedUnitLogBound (K := K) B ≤
      (100000000 : ℝ) * (B + 1 : ℕ) ^ 3 := by
  have hBpos : 0 < B := by
    by_contra h
    have : B = 0 := by omega
    subst B
    simp at hB
  have hcount := boundedIdealCount_le_degree_eight K hdeg B
  have hplaces : Fintype.card (NumberField.InfinitePlace K) ≤ 8 := by
    calc
      Fintype.card (NumberField.InfinitePlace K) ≤ Module.finrank ℚ K := by
        rw [← NumberField.InfinitePlace.sum_mult_eq]
        calc
          Fintype.card (NumberField.InfinitePlace K) =
              ∑ _w : NumberField.InfinitePlace K, 1 := by simp
          _ ≤ ∑ w : NumberField.InfinitePlace K, w.mult :=
            Finset.sum_le_sum fun w _ ↦
              Nat.one_le_iff_ne_zero.mpr w.mult_ne_zero
      _ ≤ 8 := hdeg
  have hrank : NumberField.Units.rank K ≤ 8 := by
    rw [NumberField.Units.rank]
    omega
  have hstep : (BoundedUnits.commonBoundedStepFactor (K := K) B : ℝ) ≤
      (256 : ℝ) * B := by
    unfold BoundedUnits.commonBoundedStepFactor
    push_cast
    have hp : (2 : ℝ) ^ NumberField.Units.rank K ≤ 2 ^ 8 :=
      pow_le_pow_right₀ (by norm_num) hrank
    nlinarith
  have hstepPos : 0 < (BoundedUnits.commonBoundedStepFactor (K := K) B : ℝ) := by
    unfold BoundedUnits.commonBoundedStepFactor
    positivity
  have hlog : Real.log (BoundedUnits.commonBoundedStepFactor (K := K) B : ℝ) ≤
      256 * B := by
    exact (Real.log_le_sub_one_of_pos hstepPos).trans (by nlinarith)
  unfold BoundedUnits.commonBoundedUnitLogBound
  have hcastCount :
      ((BoundedUnits.boundedIdealCount (K := K) B : ℕ) : ℝ) ≤
        (6561 * B ^ 2 + 1 : ℕ) := by exact_mod_cast hcount
  have hcastPlaces :
      (Fintype.card (NumberField.InfinitePlace K) : ℝ) ≤ 8 := by
    exact_mod_cast hplaces
  have hcastProduct :
      ((BoundedUnits.boundedIdealCount (K := K) B *
        Fintype.card (NumberField.InfinitePlace K) : ℕ) : ℝ) ≤
        ((6561 * B ^ 2 + 1 : ℕ) : ℝ) * 8 := by
    rw [Nat.cast_mul]
    exact mul_le_mul hcastCount hcastPlaces (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hnonneg : 0 ≤ Real.log
      (BoundedUnits.commonBoundedStepFactor (K := K) B : ℝ) :=
    Real.log_nonneg (by
      unfold BoundedUnits.commonBoundedStepFactor
      exact_mod_cast mul_le_mul (show 1 ≤ B by omega)
        (one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 2)) (by norm_num) (by norm_num))
  calc
    (((BoundedUnits.boundedIdealCount (K := K) B *
        Fintype.card (NumberField.InfinitePlace K) : ℕ) : ℝ) *
        Real.log (BoundedUnits.commonBoundedStepFactor (K := K) B : ℝ)) ≤
      (((6561 * B ^ 2 + 1 : ℕ) : ℝ) * 8) * (256 * B) := by
        exact mul_le_mul hcastProduct hlog hnonneg (by positivity)
    _ ≤ (100000000 : ℝ) * (B + 1 : ℕ) ^ 3 := by
      push_cast
      nlinarith [sq_nonneg (B : ℝ),
        mul_nonneg (sq_nonneg (B : ℝ)) (show (0 : ℝ) ≤ B by positivity)]

def boundedUnitIndexCoarse (B : ℕ) : ℕ :=
  40320 * 264 ^ 8 * 100000000 ^ 8 * (B + 1) ^ 24

lemma boundedUnitRegulatorNumerator_le_coarse
    (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (hdeg : Module.finrank ℚ K ≤ 8) {B : ℕ}
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B) :
    ((NumberField.Units.rank K).factorial : ℝ) *
        BoundedUnits.commonBoundedUnitLogBound (K := K) B ^
          NumberField.Units.rank K ≤
      40320 * (100000000 * (B + 1 : ℕ) ^ 3 : ℝ) ^ 8 := by
  let r := NumberField.Units.rank K
  let C : ℝ := 100000000 * (B + 1 : ℕ) ^ 3
  have hr : r ≤ 8 := by
    exact (units_rank_le_finrank K).trans hdeg
  have hfac : (r.factorial : ℝ) ≤ 40320 := by
    exact_mod_cast (Nat.factorial_le hr).trans_eq
      (by norm_num : Nat.factorial 8 = 40320)
  have hC1 : (1 : ℝ) ≤ C := by
    dsimp [C]
    have hpow : (1 : ℝ) ≤ ((B + 1 : ℕ) : ℝ) ^ 3 :=
      one_le_pow₀ (by exact_mod_cast (show 1 ≤ B + 1 by omega))
    nlinarith
  have hcommon0 : 0 ≤ BoundedUnits.commonBoundedUnitLogBound (K := K) B :=
    BoundedUnits.commonBoundedUnitLogBound_nonneg hB
  have hcommon : BoundedUnits.commonBoundedUnitLogBound (K := K) B ≤ C := by
    simpa [C] using commonBoundedUnitLogBound_le_coarse K hdeg hB
  have hcommonPow :
      BoundedUnits.commonBoundedUnitLogBound (K := K) B ^ r ≤ C ^ 8 := by
    exact (pow_le_pow_left₀ hcommon0 hcommon r).trans
      (pow_le_pow_right₀ hC1 hr)
  have hnum : (r.factorial : ℝ) *
        BoundedUnits.commonBoundedUnitLogBound (K := K) B ^ r ≤
      40320 * C ^ 8 :=
    mul_le_mul hfac hcommonPow (pow_nonneg hcommon0 _) (by norm_num)
  simpa [r, C] using hnum

lemma totallyRealDegreeEightUnitGap_pow_rank_lower
    (K : Type*) [Field K] [NumberField K]
    (hdeg : Module.finrank ℚ K ≤ 8) :
    (1 / 264 : ℝ) ^ 8 ≤
      (totallyRealDegreeEightUnitLogGap / 8) ^ NumberField.Units.rank K := by
  have hr : NumberField.Units.rank K ≤ 8 :=
    (units_rank_le_finrank K).trans hdeg
  have hd0 : (0 : ℝ) ≤ 1 / 264 := by norm_num
  have hd1 : (1 / 264 : ℝ) ≤ 1 := by norm_num
  exact (pow_le_pow_of_le_one hd0 hd1 hr).trans
    (pow_le_pow_left₀ hd0
      one_div_264_le_totallyRealDegreeEightUnitLogGap_div_eight _)

lemma boundedUnitRegulatorQuotient_le_coarse_real
    (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (hdeg : Module.finrank ℚ K ≤ 8) {B : ℕ}
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B) :
    BoundedUnits.boundedUnitRegulatorUpper (K := K) B /
        (totallyRealDegreeEightUnitLogGap / 8) ^ NumberField.Units.rank K ≤
      (boundedUnitIndexCoarse B : ℝ) := by
  let C : ℝ := 100000000 * (B + 1 : ℕ) ^ 3
  let d : ℝ := 1 / 264
  have hnum := boundedUnitRegulatorNumerator_le_coarse K hdeg hB
  have hden := totallyRealDegreeEightUnitGap_pow_rank_lower K hdeg
  have hnum0 : 0 ≤ BoundedUnits.boundedUnitRegulatorUpper (K := K) B := by
    unfold BoundedUnits.boundedUnitRegulatorUpper
    exact mul_nonneg (Nat.cast_nonneg _)
      (pow_nonneg (BoundedUnits.commonBoundedUnitLogBound_nonneg hB) _)
  have hdenPos : 0 < d ^ 8 := pow_pos (by dsimp [d]; norm_num) _
  have hquot :
      BoundedUnits.boundedUnitRegulatorUpper (K := K) B /
          (totallyRealDegreeEightUnitLogGap / 8) ^ NumberField.Units.rank K ≤
        40320 * C ^ 8 / d ^ 8 := by
    exact div_le_div₀ (by positivity) (by
      simpa [BoundedUnits.boundedUnitRegulatorUpper, C] using hnum)
      hdenPos (by simpa [d] using hden)
  have hcoarse : 40320 * C ^ 8 / d ^ 8 =
      (boundedUnitIndexCoarse B : ℝ) := by
    dsimp [C, d, boundedUnitIndexCoarse]
    push_cast
    norm_num
    ring
  exact hquot.trans_eq hcoarse

lemma boundedUnitIndexUpper_le_coarse
    (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (hdeg : Module.finrank ℚ K ≤ 8) {B : ℕ}
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B) :
    BoundedUnits.boundedUnitIndexUpper (K := K)
        (totallyRealDegreeEightUnitLogGap / 8) B ≤
      boundedUnitIndexCoarse B := by
  unfold BoundedUnits.boundedUnitIndexUpper
  rw [Nat.ceil_le]
  exact boundedUnitRegulatorQuotient_le_coarse_real K hdeg hB

lemma sum_norm_complexLog_le_sum_logHeight_of_positive
    {K : Type*} [Field K] [NumberField K] {n : ℕ}
    (φ : K →+* ℂ) (ρ : K →+* ℝ) (hφρ : ∀ x, φ x = (ρ x : ℂ))
    (alpha : Fin n → K) (hpos : ∀ i, 0 < ρ (alpha i)) :
    (∑ i, ‖Complex.log (φ (alpha i))‖) ≤
      ∑ i, Height.logHeight₁ (alpha i) := by
  apply Finset.sum_le_sum
  intro i _hi
  have hne : alpha i ≠ 0 := by
    intro h
    have hi := hpos i
    rw [h, map_zero] at hi
    exact (lt_irrefl 0 hi)
  have habs := numberField_abs_log_norm_embedding_le_logHeight φ hne
  have hreal : φ (alpha i) = ((ρ (alpha i) : ℝ) : ℂ) := hφρ _
  rw [hreal, ← Complex.ofReal_log (hpos i).le, Complex.norm_real,
    Real.norm_eq_abs]
  rw [hreal, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpos i)] at habs
  exact habs

lemma combinedSquaredProductBases_sum_logHeight_le
    {K : Type*} [Field K] [NumberField K] {r : ℕ}
    (W : K) (eps : Fin r → K) {Q C : ℝ}
    (hW : Height.logHeight₁ W ≤ Q)
    (heps : ∀ i, Height.logHeight₁ (eps i) ≤ C) :
    (∑ i, Height.logHeight₁ (combinedSquaredProductBases W eps i)) ≤
      Q + (r : ℝ) * (2 * C) := by
  rw [Fin.sum_univ_succ]
  dsimp [combinedSquaredProductBases]
  calc
    Height.logHeight₁ W + ∑ i, Height.logHeight₁ (eps i ^ 2) ≤
        Q + ∑ _i : Fin r, (2 * C) := by
      gcongr with i
      rw [Height.logHeight₁_pow]
      norm_num
      linarith [heps i]
    _ = Q + (r : ℝ) * (2 * C) := by simp

lemma boundedUnitSquares_sum_logHeight_le
    {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (hdeg : Module.finrank ℚ K ≤ 8) {B : ℕ}
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B) :
    (∑ i : Fin (NumberField.Units.rank K),
        Height.logHeight₁
          ((((Units.map (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom
              (BoundedUnits.boundedFundSystem hB i) : Kˣ) : K)) ^ 2)) ≤
      128 * BoundedUnits.commonBoundedUnitLogBound (K := K) B := by
  have hr : NumberField.Units.rank K ≤ 8 :=
    (units_rank_le_finrank K).trans hdeg
  have hC0 := BoundedUnits.commonBoundedUnitLogBound_nonneg hB
  calc
    (∑ i : Fin (NumberField.Units.rank K),
        Height.logHeight₁
          ((((Units.map (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom
              (BoundedUnits.boundedFundSystem hB i) : Kˣ) : K)) ^ 2)) =
      ∑ _i : Fin (NumberField.Units.rank K),
        (2 * Height.logHeight₁
          (((BoundedUnits.boundedFundSystem hB _ :
            (NumberField.RingOfIntegers K)ˣ) :
              NumberField.RingOfIntegers K) : K)) := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [Height.logHeight₁_pow]
        rfl
    _ ≤ ∑ _i : Fin (NumberField.Units.rank K),
        (16 * BoundedUnits.commonBoundedUnitLogBound (K := K) B) := by
      apply Finset.sum_le_sum
      intro i _hi
      have hi := boundedFundSystem_logHeight_le_degree_eight K hdeg hB i
      calc
        2 * Height.logHeight₁
            (((BoundedUnits.boundedFundSystem hB i :
              (NumberField.RingOfIntegers K)ˣ) :
                NumberField.RingOfIntegers K) : K) ≤
            2 * (8 * BoundedUnits.commonBoundedUnitLogBound (K := K) B) :=
          mul_le_mul_of_nonneg_left hi (by norm_num)
        _ = 16 * BoundedUnits.commonBoundedUnitLogBound (K := K) B := by ring
    _ = (NumberField.Units.rank K : ℝ) *
        (16 * BoundedUnits.commonBoundedUnitLogBound (K := K) B) := by simp
    _ ≤ 128 * BoundedUnits.commonBoundedUnitLogBound (K := K) B := by
      have hrR : (NumberField.Units.rank K : ℝ) ≤ 8 := by exact_mod_cast hr
      nlinarith

lemma abs_log_le_two_mul_abs_sub_one {z : ℝ} (hz : 0 < z)
    (hsmall : |z - 1| ≤ 1 / 2) :
    |Real.log z| ≤ 2 * |z - 1| := by
  have hzhalf : (1 / 2 : ℝ) ≤ z := by
    have := (abs_le.mp hsmall).1
    linarith
  by_cases hzone : 1 ≤ z
  · rw [abs_of_nonneg (Real.log_nonneg hzone), abs_of_nonneg (sub_nonneg.mpr hzone)]
    exact (Real.log_le_sub_one_of_pos hz).trans (by linarith)
  · have hzle : z ≤ 1 := le_of_not_ge hzone
    rw [abs_of_nonpos (Real.log_nonpos hz.le hzle),
      abs_of_nonpos (sub_nonpos.mpr hzle)]
    have hinv : Real.log z⁻¹ ≤ z⁻¹ - 1 :=
      Real.log_le_sub_one_of_pos (inv_pos.mpr hz)
    rw [Real.log_inv] at hinv
    have hmul : 1 - z ≤ 2 * z * (1 - z) := by
      have hz2 : 1 ≤ 2 * z := by linarith
      simpa using (mul_le_mul_of_nonneg_right hz2 (sub_nonneg.mpr hzle))
    have hfrac : z⁻¹ - 1 ≤ 2 * (1 - z) := by
      rw [show z⁻¹ - 1 = (1 - z) / z by field_simp]
      exact (div_le_iff₀ hz).2 (by nlinarith)
    nlinarith

lemma abs_log_pow_le_of_close {z : ℝ} (hz : 0 < z)
    (hsmall : |z - 1| ≤ 1 / 2) (m : ℕ) :
    |Real.log (z ^ m)| ≤ (2 * m : ℕ) * |z - 1| := by
  rw [Real.log_pow, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ m by positivity)]
  calc
    (m : ℝ) * |Real.log z| ≤ (m : ℝ) * (2 * |z - 1|) :=
      mul_le_mul_of_nonneg_left
        (abs_log_le_two_mul_abs_sub_one hz hsmall) (Nat.cast_nonneg m)
    _ = ((2 * m : ℕ) : ℝ) * |z - 1| := by push_cast; ring

lemma numberField_logHeight_intCast
    (K : Type*) [Field K] [NumberField K] (z : ℤ) :
    Height.logHeight₁ (z : K) =
      (Module.finrank ℚ K : ℝ) * Real.log (z.natAbs : ℝ) := by
  rcases z.eq_nat_or_neg with ⟨n, rfl | rfl⟩
  · simpa using numberField_logHeight_natCast K n
  · rw [Int.cast_neg, Height.logHeight₁_neg]
    simpa using numberField_logHeight_natCast K n

lemma numberField_logHeight_intRatio_le
    (K : Type*) [Field K] [NumberField K]
    {a b : ℤ} {J : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (haJ : a.natAbs ≤ J) (hbJ : b.natAbs ≤ J)
    (hdeg : Module.finrank ℚ K ≤ 8) :
    Height.logHeight₁ ((a : K) / (b : K)) ≤
      16 * Real.log (J + 1 : ℕ) := by
  have haPos : 0 < a.natAbs := Int.natAbs_pos.mpr ha
  have hbPos : 0 < b.natAbs := Int.natAbs_pos.mpr hb
  have hlogA : Real.log (a.natAbs : ℝ) ≤ Real.log (J + 1 : ℕ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast (show a.natAbs ≤ J + 1 by omega))
  have hlogB : Real.log (b.natAbs : ℝ) ≤ Real.log (J + 1 : ℕ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast (show b.natAbs ≤ J + 1 by omega))
  have hdegR : (Module.finrank ℚ K : ℝ) ≤ 8 := by exact_mod_cast hdeg
  calc
    Height.logHeight₁ ((a : K) / (b : K)) ≤
        Height.logHeight₁ (a : K) + Height.logHeight₁ (b : K) :=
      numberField_logHeight_div_le K _ _
    _ = (Module.finrank ℚ K : ℝ) * Real.log (a.natAbs : ℝ) +
        (Module.finrank ℚ K : ℝ) * Real.log (b.natAbs : ℝ) := by
      rw [numberField_logHeight_intCast, numberField_logHeight_intCast]
    _ ≤ 16 * Real.log (J + 1 : ℕ) := by
      have hlog0 : 0 ≤ Real.log (J + 1 : ℕ) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ J + 1 by omega))
      have ha0 : 0 ≤ Real.log (a.natAbs : ℝ) :=
        Real.log_nonneg (by exact_mod_cast haPos)
      have hb0 : 0 ≤ Real.log (b.natAbs : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hbPos)
      nlinarith

lemma simultaneousPell_secondary_coordinate_le
    {γ₁ γ₂ γ₃ H x₁ x₂ x₃ J : ℕ} {β₁₂ β₁₃ : ℤ}
    (hPell : SimultaneousPellZ (γ₁ : ℤ) (γ₂ : ℤ) (γ₃ : ℤ)
      β₁₂ β₁₃ (x₁ : ℤ) (x₂ : ℤ) (x₃ : ℤ))
    (hJ₁₂ : β₁₂.natAbs ≤ J) (hJ₁₃ : β₁₃.natAbs ≤ J)
    (hγ₁ : 0 < γ₁) (hγ₁H : γ₁ ≤ H)
    (hγ₂ : 0 < γ₂) (hγ₃ : 0 < γ₃)
    (hx₁ : 0 < x₁) :
    (x₂ : ℝ) ≤ H * x₁ + J ∧ (x₃ : ℝ) ≤ H * x₁ + J := by
  have hβ₁₂lower : -(J : ℝ) ≤ (β₁₂ : ℝ) := by
    have habs : |(β₁₂ : ℝ)| ≤ J := by
      rw [← Int.cast_abs, ← Nat.cast_natAbs]
      exact_mod_cast hJ₁₂
    exact (abs_le.mp habs).1
  have hβ₁₃lower : -(J : ℝ) ≤ (β₁₃ : ℝ) := by
    have habs : |(β₁₃ : ℝ)| ≤ J := by
      rw [← Int.cast_abs, ← Nat.cast_natAbs]
      exact_mod_cast hJ₁₃
    exact (abs_le.mp habs).1
  have h12 : (γ₁ : ℝ) * (x₁ : ℝ) ^ 2 -
      (γ₂ : ℝ) * (x₂ : ℝ) ^ 2 = (β₁₂ : ℝ) := by exact_mod_cast hPell.1
  have h13 : (γ₁ : ℝ) * (x₁ : ℝ) ^ 2 -
      (γ₃ : ℝ) * (x₃ : ℝ) ^ 2 = (β₁₃ : ℝ) := by exact_mod_cast hPell.2
  have hγ₁R : (γ₁ : ℝ) ≤ H := by exact_mod_cast hγ₁H
  have hγ₂R : (1 : ℝ) ≤ γ₂ := by exact_mod_cast hγ₂
  have hγ₃R : (1 : ℝ) ≤ γ₃ := by exact_mod_cast hγ₃
  have hx₁R : (1 : ℝ) ≤ x₁ := by exact_mod_cast hx₁
  have hsq2 : (x₂ : ℝ) ^ 2 ≤ H * (x₁ : ℝ) ^ 2 + J := by nlinarith
  have hsq3 : (x₃ : ℝ) ^ 2 ≤ H * (x₁ : ℝ) ^ 2 + J := by nlinarith
  have htargetSq : H * (x₁ : ℝ) ^ 2 + J ≤
      (H * (x₁ : ℝ) + J) ^ 2 := by
    have hH : (1 : ℝ) ≤ H := by exact_mod_cast hγ₁.trans_le hγ₁H
    have hJ0 : (0 : ℝ) ≤ J := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hH) (sq_nonneg (x₁ : ℝ)),
      mul_nonneg hJ0 (by nlinarith : (0 : ℝ) ≤ J + 2 * H * x₁ - 1)]
  constructor
  · exact le_of_sq_le_sq (hsq2.trans htargetSq) (by positivity)
  · exact le_of_sq_le_sq (hsq3.trans htargetSq) (by positivity)

lemma realPell_leftUnit_logHeight_le_coarse
    {K : Type*} [Field K] [NumberField K]
    {s₁ s₂ s₃ : K} {γ₁ γ₂ γ₃ H x₁ x₂ x₃ J : ℕ}
    {β₁₂ β₁₃ : ℤ}
    (hs₁ : s₁ ^ 2 = (γ₁ : K)) (hs₂ : s₂ ^ 2 = (γ₂ : K))
    (hs₃ : s₃ ^ 2 = (γ₃ : K))
    (hPell : SimultaneousPellZ (γ₁ : ℤ) (γ₂ : ℤ) (γ₃ : ℤ)
      β₁₂ β₁₃ (x₁ : ℤ) (x₂ : ℤ) (x₃ : ℤ))
    (hJ₁₂ : β₁₂.natAbs ≤ J) (hJ₁₃ : β₁₃.natAbs ≤ J)
    (hdeg : Module.finrank ℚ K ≤ 8)
    (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂) (hγ₃ : 0 < γ₃)
    (hγ₁H : γ₁ ≤ H) (hγ₂H : γ₂ ≤ H) (hγ₃H : γ₃ ≤ H)
    (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) (hx₃ : 0 < x₃) :
    Height.logHeight₁
        (pellValueMinus s₁ s₂ (x₁ : ℤ) (x₂ : ℤ) /
          pellValueMinus s₁ s₃ (x₁ : ℤ) (x₃ : ℤ)) ≤
      100 * (1 + Real.log (H + J + 1 : ℕ) + Real.log (x₁ : ℝ)) := by
  have hcoord := simultaneousPell_secondary_coordinate_le hPell hJ₁₂ hJ₁₃
    hγ₁ hγ₁H hγ₂ hγ₃ hx₁
  have hHJpos : (0 : ℝ) < ((H + J + 1 : ℕ) : ℝ) := by positivity
  have hx₁R : (1 : ℝ) ≤ x₁ := by exact_mod_cast hx₁
  have hprodPos : 0 < ((H + J + 1 : ℕ) : ℝ) * (x₁ : ℝ) := by positivity
  have hx2Bound : (x₂ : ℝ) ≤ ((H + J + 1 : ℕ) : ℝ) * x₁ := by
    push_cast
    nlinarith
  have hx3Bound : (x₃ : ℝ) ≤ ((H + J + 1 : ℕ) : ℝ) * x₁ := by
    push_cast
    nlinarith
  have hlog2 : Real.log (x₂ : ℝ) ≤
      Real.log (H + J + 1 : ℕ) + Real.log (x₁ : ℝ) := by
    calc
      Real.log (x₂ : ℝ) ≤ Real.log (((H + J + 1 : ℕ) : ℝ) * x₁) :=
        Real.log_le_log (by positivity) hx2Bound
      _ = _ := by rw [Real.log_mul hHJpos.ne' (by positivity)]
  have hlog3 : Real.log (x₃ : ℝ) ≤
      Real.log (H + J + 1 : ℕ) + Real.log (x₁ : ℝ) := by
    calc
      Real.log (x₃ : ℝ) ≤ Real.log (((H + J + 1 : ℕ) : ℝ) * x₁) :=
        Real.log_le_log (by positivity) hx3Bound
      _ = _ := by rw [Real.log_mul hHJpos.ne' (by positivity)]
  have hbase := (numberField_logHeight_pellRatios_le K s₁ s₂ s₃
    hs₁ hs₂ hs₃ hdeg hγ₁ hγ₂ hγ₃ hγ₁H hγ₂H hγ₃H hx₁ hx₂ hx₃).1
  have hlogH : Real.log (H : ℝ) ≤ Real.log (H + J + 1 : ℕ) :=
    Real.log_le_log (by exact_mod_cast hγ₁.trans_le hγ₁H)
      (by exact_mod_cast (show H ≤ H + J + 1 by omega))
  have hlog2const : Real.log 2 ≤ 1 := Real.log_two_lt_d9.le.trans (by norm_num)
  have hlogHJ0 : 0 ≤ Real.log (H + J + 1 : ℕ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ H + J + 1 by omega))
  have hlogx0 : 0 ≤ Real.log (x₁ : ℝ) := Real.log_nonneg hx₁R
  nlinarith

def pellMinkowskiControl (H : ℕ) : ℕ :=
  258 * ((40320 * (H + 1) ^ 24) ^ 2 + 1)

noncomputable def pellClassControl (H : ℕ) : ℝ :=
  (6 : ℝ) ^ 8 * ((40320 : ℝ) * (H + 1 : ℕ) ^ 24) ^ 2

noncomputable def pellCommonUnitControl (H : ℕ) : ℝ :=
  100000000 * (pellMinkowskiControl H + 1 : ℕ) ^ 3

def pellIndexControl (H : ℕ) : ℕ :=
  boundedUnitIndexCoarse (pellMinkowskiControl H)

noncomputable def pellSupportControl (J : ℕ) : ℝ := 24 * (J + 1)

noncomputable def pellPrimeGeneratorControl (H J : ℕ) : ℝ :=
  128 * pellCommonUnitControl H +
    136 * pellClassControl H * Real.log (J + 1 : ℕ)

noncomputable def pellPrimeProductControl (H J : ℕ) : ℝ :=
  pellSupportControl J * (J + 1 : ℕ) ^ 16 * pellPrimeGeneratorControl H J

noncomputable def pellRatioControl (J : ℕ) : ℝ :=
  16 * Real.log (J + 1 : ℕ)

noncomputable def pellLeadingControl (H J : ℕ) : ℝ :=
  (2 * (pellClassControl H * pellIndexControl H)) * pellRatioControl J +
    (2 * pellIndexControl H : ℕ) * pellPrimeProductControl H J

noncomputable def pellLeftUnitControl (H J x : ℕ) : ℝ :=
  100 * (1 + Real.log (H + J + 1 : ℕ) + Real.log (x : ℝ))

noncomputable def pellResidualControl (H J x : ℕ) : ℝ :=
  pellClassControl H * pellLeftUnitControl H J x + pellPrimeProductControl H J

noncomputable def pellCoordinateBaseControl (H J x : ℕ) : ℝ :=
  1 + pellCommonUnitControl H +
    (pellIndexControl H : ℝ) * (2 * pellResidualControl H J x)

noncomputable def pellCoefficientControl (H J x : ℕ) : ℝ :=
  40320 * (264 : ℝ) ^ 8 * pellCoordinateBaseControl H J x ^ 8

noncomputable def pellAbsorptionCoordinateBaseControl (H J : ℕ) : ℝ :=
  1 + pellCommonUnitControl H +
    (pellIndexControl H : ℝ) * (2 * pellLeadingControl H J)

noncomputable def pellAbsorptionCoefficientControl (H J : ℕ) : ℝ :=
  40320 * (264 : ℝ) ^ 8 *
    pellAbsorptionCoordinateBaseControl H J ^ 8

noncomputable def pellUnitBoxControl (H J x : ℕ) : ℝ :=
  pellAbsorptionCoefficientControl H J + 1 +
    2 * pellIndexControl H * (pellCoefficientControl H J x + 2)

noncomputable def pellThresholdControl (H J x : ℕ) : ℝ :=
  (1000000000000000000000000000000 : ℝ) +
    3 * Real.log (H + 1 : ℕ) +
    Real.log (2 * pellCoefficientControl H J x + 5) +
    Real.log (2 * pellUnitBoxControl H J x + 3) +
    2 * (pellLeadingControl H J + 128 * pellCommonUnitControl H)

lemma degreeEightMinkowskiNatBound_le_pellMinkowskiControl (H : ℕ) :
    degreeEightMinkowskiNatBound ((40320 * H ^ 24) ^ 2) ≤
      pellMinkowskiControl H := by
  calc
    degreeEightMinkowskiNatBound ((40320 * H ^ 24) ^ 2) ≤
        258 * (((40320 * H ^ 24) ^ 2) + 1) :=
      degreeEightMinkowskiNatBound_le _
    _ ≤ 258 * ((40320 * (H + 1) ^ 24) ^ 2 + 1) := by
      gcongr <;> omega
    _ = pellMinkowskiControl H := rfl

lemma realPellField_classNumber_le_control
    {γ₁ γ₂ γ₃ H : ℕ}
    (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂) (hγ₃ : 0 < γ₃)
    (hγ₁H : γ₁ ≤ H) (hγ₂H : γ₂ ≤ H) (hγ₃H : γ₃ ≤ H) :
    let K := realPellField γ₁ γ₂ γ₃
    let _ : Algebra ℚ K := K.algebra'
    let _ : NumberField K := realPellFieldNumberField γ₁ γ₂ γ₃
    (NumberField.classNumber K : ℝ) ≤ pellClassControl H := by
  dsimp only
  have h := realPellField_classNumber_le hγ₁ hγ₂ hγ₃ hγ₁H hγ₂H hγ₃H
  dsimp only at h
  exact h.trans (by
    unfold pellClassControl
    gcongr
    exact (show H ≤ H + 1 by omega))

lemma pellCommonPrimeSupport_card_le_control
    {K : Type*} [Field K] [NumberField K]
    {β₁₂ β₁₃ β₂₃ : ℤ} {J : ℕ}
    (hβ₁₂ : β₁₂ ≠ 0) (hβ₁₃ : β₁₃ ≠ 0) (hβ₂₃ : β₂₃ ≠ 0)
    (hJ₁₂ : β₁₂.natAbs ≤ J) (hJ₁₃ : β₁₃.natAbs ≤ J)
    (hJ₂₃ : β₂₃.natAbs ≤ J)
    (hdeg : Module.finrank ℚ K ≤ 8) :
    (Nat.card (pellCommonPrimeSupport
        (Units.mk0 (β₁₂ : K) (Int.cast_ne_zero.mpr hβ₁₂))
        (Units.mk0 (β₁₃ : K) (Int.cast_ne_zero.mpr hβ₁₃))
        (Units.mk0 (β₂₃ : K) (Int.cast_ne_zero.mpr hβ₂₃))) : ℝ) ≤
      pellSupportControl J := by
  have hcard := pellCommonIntegerPrimeSupport_card_le
    (K := K) β₁₂ β₁₃ β₂₃ hβ₁₂ hβ₁₃ hβ₂₃
  have hpf12 := (primeFactors_card_le_log_two
    (Int.natAbs_ne_zero.mpr hβ₁₂)).trans (Nat.log_mono_right hJ₁₂)
  have hpf13 := (primeFactors_card_le_log_two
    (Int.natAbs_ne_zero.mpr hβ₁₃)).trans (Nat.log_mono_right hJ₁₃)
  have hpf23 := (primeFactors_card_le_log_two
    (Int.natAbs_ne_zero.mpr hβ₂₃)).trans (Nat.log_mono_right hJ₂₃)
  have hlogJ : Nat.log 2 J ≤ J + 1 := (Nat.log_le_self 2 J).trans (by omega)
  unfold pellSupportControl
  exact_mod_cast hcard.trans (by nlinarith [hdeg, hpf12, hpf13, hpf23, hlogJ])

lemma realPell_commonBoundedUnitLogBound_le_control
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {H : ℕ} (hdeg : Module.finrank ℚ K ≤ 8) {B : ℕ}
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B)
    (hBH : B ≤ pellMinkowskiControl H) :
    BoundedUnits.commonBoundedUnitLogBound (K := K) B ≤
      pellCommonUnitControl H := by
  calc
    BoundedUnits.commonBoundedUnitLogBound (K := K) B ≤
        100000000 * (B + 1 : ℕ) ^ 3 :=
      commonBoundedUnitLogBound_le_coarse K hdeg hB
    _ ≤ 100000000 * (pellMinkowskiControl H + 1 : ℕ) ^ 3 := by
      gcongr
    _ = pellCommonUnitControl H := rfl

lemma realPell_boundedUnitIndexUpper_le_control
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {H : ℕ} (hdeg : Module.finrank ℚ K ≤ 8) {B : ℕ}
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B)
    (hBH : B ≤ pellMinkowskiControl H) :
    BoundedUnits.boundedUnitIndexUpper (K := K)
        (totallyRealDegreeEightUnitLogGap / 8) B ≤
      pellIndexControl H := by
  calc
    BoundedUnits.boundedUnitIndexUpper (K := K)
        (totallyRealDegreeEightUnitLogGap / 8) B ≤ boundedUnitIndexCoarse B :=
      boundedUnitIndexUpper_le_coarse K hdeg hB
    _ ≤ boundedUnitIndexCoarse (pellMinkowskiControl H) := by
      unfold boundedUnitIndexCoarse
      gcongr
    _ = pellIndexControl H := rfl

lemma test_boundedPrimeClassHeightMajorant_le_control
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {H J B : ℕ} (hdeg : Module.finrank ℚ K ≤ 8)
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B)
    (hBH : B ≤ pellMinkowskiControl H)
    (hclass : (NumberField.classNumber K : ℝ) ≤ pellClassControl H) :
    test_boundedPrimeClassHeightMajorant K B J ≤
      pellPrimeGeneratorControl H J := by
  have hrank : NumberField.Units.rank K ≤ 8 :=
    (units_rank_le_finrank K).trans hdeg
  have hrankR : (NumberField.Units.rank K : ℝ) ≤ 8 := by
    exact_mod_cast hrank
  have hcommon := realPell_commonBoundedUnitLogBound_le_control hdeg hB hBH
  have hcommon0 := BoundedUnits.commonBoundedUnitLogBound_nonneg hB
  have hlogJ : Real.log (J : ℝ) ≤ Real.log (J + 1 : ℕ) := by
    by_cases hJ0 : J = 0
    · subst J
      simp
    · exact Real.log_le_log (by positivity) (by exact_mod_cast (show J ≤ J + 1 by omega))
  have hlogJ1 : 0 ≤ Real.log (J + 1 : ℕ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ J + 1 by omega))
  unfold test_boundedPrimeClassHeightMajorant pellPrimeGeneratorControl
  have hfirst :
      2 * (NumberField.Units.rank K : ℝ) ^ 2 *
          BoundedUnits.commonBoundedUnitLogBound (K := K) B ≤
        128 * pellCommonUnitControl H := by
    have hrankSq : (NumberField.Units.rank K : ℝ) ^ 2 ≤ 64 := by
      nlinarith [sq_nonneg ((NumberField.Units.rank K : ℝ) - 8)]
    calc
      2 * (NumberField.Units.rank K : ℝ) ^ 2 *
          BoundedUnits.commonBoundedUnitLogBound (K := K) B ≤
          128 * BoundedUnits.commonBoundedUnitLogBound (K := K) B := by
        gcongr
        nlinarith
      _ ≤ 128 * pellCommonUnitControl H := by gcongr
  have hcoef : (((2 * NumberField.Units.rank K + 1 : ℕ) : ℝ)) ≤ 17 := by
    exact_mod_cast (by omega : 2 * NumberField.Units.rank K + 1 ≤ 17)
  have hsecond :
      (((2 * NumberField.Units.rank K + 1 : ℕ) : ℝ)) *
          ((NumberField.classNumber K : ℝ) * (8 * Real.log (J : ℝ))) ≤
        136 * pellClassControl H * Real.log (J + 1 : ℕ) := by
    have hclass0 : 0 ≤ (NumberField.classNumber K : ℝ) := by positivity
    have hclassC0 : 0 ≤ pellClassControl H := hclass0.trans hclass
    have hlogJ0 : 0 ≤ Real.log (J : ℝ) := by
      by_cases hJ0 : J = 0
      · subst J
        simp
      · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ J by omega))
    calc
      (((2 * NumberField.Units.rank K + 1 : ℕ) : ℝ)) *
          ((NumberField.classNumber K : ℝ) * (8 * Real.log (J : ℝ))) ≤
          17 * ((NumberField.classNumber K : ℝ) * (8 * Real.log (J : ℝ))) := by
        gcongr
      _ ≤ 17 * (pellClassControl H * (8 * Real.log (J : ℝ))) := by
        gcongr
      _ ≤ 17 * (pellClassControl H *
          (8 * Real.log (J + 1 : ℕ))) := by
        gcongr
      _ = 136 * pellClassControl H * Real.log (J + 1 : ℕ) := by ring
  linarith

lemma pellCommonUnitControl_nonneg (H : ℕ) : 0 ≤ pellCommonUnitControl H := by
  unfold pellCommonUnitControl
  positivity

lemma pellClassControl_nonneg (H : ℕ) : 0 ≤ pellClassControl H := by
  unfold pellClassControl
  positivity

lemma pellSupportControl_nonneg (J : ℕ) : 0 ≤ pellSupportControl J := by
  unfold pellSupportControl
  positivity

lemma pellPrimeGeneratorControl_nonneg (H J : ℕ) :
    0 ≤ pellPrimeGeneratorControl H J := by
  unfold pellPrimeGeneratorControl
  have hlog : 0 ≤ Real.log (J + 1 : ℕ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ J + 1 by omega))
  exact add_nonneg
    (mul_nonneg (by norm_num) (pellCommonUnitControl_nonneg H))
    (mul_nonneg (mul_nonneg (by norm_num) (pellClassControl_nonneg H)) hlog)

lemma pellPrimeProductControl_nonneg (H J : ℕ) :
    0 ≤ pellPrimeProductControl H J := by
  unfold pellPrimeProductControl
  exact mul_nonneg
    (mul_nonneg (pellSupportControl_nonneg J) (by positivity))
    (pellPrimeGeneratorControl_nonneg H J)

lemma pellRatioControl_nonneg (J : ℕ) : 0 ≤ pellRatioControl J := by
  unfold pellRatioControl
  exact mul_nonneg (by norm_num)
    (Real.log_nonneg (by exact_mod_cast (show 1 ≤ J + 1 by omega)))

lemma pellLeadingControl_nonneg (H J : ℕ) : 0 ≤ pellLeadingControl H J := by
  unfold pellLeadingControl
  exact add_nonneg
    (mul_nonneg (mul_nonneg (by norm_num)
      (mul_nonneg (pellClassControl_nonneg H) (by positivity)))
      (pellRatioControl_nonneg J))
    (mul_nonneg (by positivity) (pellPrimeProductControl_nonneg H J))

lemma pellLeftUnitControl_nonneg {H J x : ℕ} (hx : 0 < x) :
    0 ≤ pellLeftUnitControl H J x := by
  unfold pellLeftUnitControl
  have hxlog : 0 ≤ Real.log (x : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hx)
  have hHJlog : 0 ≤ Real.log (H + J + 1 : ℕ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ H + J + 1 by omega))
  positivity

lemma pellResidualControl_nonneg {H J x : ℕ} (hx : 0 < x) :
    0 ≤ pellResidualControl H J x := by
  unfold pellResidualControl
  exact add_nonneg
    (mul_nonneg (pellClassControl_nonneg H)
      (pellLeftUnitControl_nonneg hx))
    (pellPrimeProductControl_nonneg H J)

lemma realPell_primeProductHeightMajorant_le_control
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {H J B : ℕ} {S : Type*} [Fintype S]
    (hdeg : Module.finrank ℚ K ≤ 8)
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B)
    (hBH : B ≤ pellMinkowskiControl H)
    (hclass : (NumberField.classNumber K : ℝ) ≤ pellClassControl H)
    (hcard : (Fintype.card S : ℝ) ≤ pellSupportControl J) :
    ((Fintype.card S : ℝ) * (J ^ 16 : ℝ)) *
        test_boundedPrimeClassHeightMajorant K B J ≤
      pellPrimeProductControl H J := by
  have hmajor := test_boundedPrimeClassHeightMajorant_le_control
    (J := J) hdeg hB hBH hclass
  have hmajor0 : 0 ≤ test_boundedPrimeClassHeightMajorant K B J := by
    unfold test_boundedPrimeClassHeightMajorant
    have hcommon0 := BoundedUnits.commonBoundedUnitLogBound_nonneg hB
    by_cases hJ0 : J = 0
    · subst J
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, CharP.cast_eq_zero, Real.log_zero,
    mul_zero, add_zero, ge_iff_le]
      positivity
    · have hlogJ : 0 ≤ Real.log (J : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ J by omega))
      positivity
  have hJpow : (J ^ 16 : ℝ) ≤ (J + 1 : ℕ) ^ 16 := by
    exact_mod_cast (Nat.pow_le_pow_left (show J ≤ J + 1 by omega) 16)
  unfold pellPrimeProductControl
  exact mul_le_mul
    (mul_le_mul hcard hJpow (by positivity) (pellSupportControl_nonneg J))
    hmajor hmajor0
    (mul_nonneg (pellSupportControl_nonneg J) (by positivity))

lemma realPell_ratioHeight_le_control
    {K : Type*} [Field K] [NumberField K]
    {a b : ℤ} {J : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (haJ : a.natAbs ≤ J) (hbJ : b.natAbs ≤ J)
    (hdeg : Module.finrank ℚ K ≤ 8) :
    Height.logHeight₁ ((a : K) / (b : K)) ≤ pellRatioControl J := by
  simpa only [pellRatioControl] using
    numberField_logHeight_intRatio_le K ha hb haJ hbJ hdeg

lemma realPell_leadingHeightMajorant_le_control
    {K : Type*} [Field K] [NumberField K]
    {H J I : ℕ} {QP : ℝ}
    (hclass : (NumberField.classNumber K : ℝ) ≤ pellClassControl H)
    (hI : I ≤ pellIndexControl H)
    (hQP0 : 0 ≤ QP) (hQP : QP ≤ pellPrimeProductControl H J) :
    (2 * (NumberField.classNumber K * I) : ℕ) * pellRatioControl J +
        (2 * I : ℕ) * QP ≤ pellLeadingControl H J := by
  have hclass0 : 0 ≤ (NumberField.classNumber K : ℝ) := by exact_mod_cast Nat.zero_le _
  have hIR : (I : ℝ) ≤ pellIndexControl H := by exact_mod_cast hI
  have hclassIR : (NumberField.classNumber K : ℝ) * I ≤
      pellClassControl H * pellIndexControl H := by
    exact mul_le_mul hclass hIR (Nat.cast_nonneg _) (pellClassControl_nonneg H)
  have htwoClass :
      ((2 * (NumberField.classNumber K * I) : ℕ) : ℝ) ≤
        2 * (pellClassControl H * pellIndexControl H) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      (mul_le_mul_of_nonneg_left hclassIR (by norm_num : (0 : ℝ) ≤ 2))
  have htwoI : ((2 * I : ℕ) : ℝ) ≤
      ((2 * pellIndexControl H : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_le_mul_left 2 hI
  rw [pellLeadingControl]
  exact add_le_add
    (mul_le_mul_of_nonneg_right htwoClass (pellRatioControl_nonneg J))
    (mul_le_mul htwoI hQP hQP0 (Nat.cast_nonneg _))

lemma boundedUnitCoordinateRealBound_le_control
    {K : Type*} [Field K] [NumberField K]
    {C Q Qc : ℝ} {B I Ic : ℕ}
    (hdeg : Module.finrank ℚ K ≤ 8)
    (hC0 : 0 ≤ C)
    (hcommon : BoundedUnits.commonBoundedUnitLogBound (K := K) B ≤ C)
    (hindex : I ≤ Ic) (hQ0 : 0 ≤ Q) (hQ : Q ≤ Qc)
    (hQc0 : 0 ≤ Qc) :
    ((NumberField.Units.rank K).factorial *
        (max (BoundedUnits.commonBoundedUnitLogBound (K := K) B)
          ((I : ℝ) * (2 * Q))) ^ NumberField.Units.rank K) /
        (totallyRealDegreeEightUnitLogGap / 8) ^ NumberField.Units.rank K ≤
      40320 * (264 : ℝ) ^ 8 *
        (1 + C + (Ic : ℝ) * (2 * Qc)) ^ 8 := by
  let r := NumberField.Units.rank K
  let base : ℝ := 1 + C + (Ic : ℝ) * (2 * Qc)
  let common := BoundedUnits.commonBoundedUnitLogBound (K := K) B
  let coord : ℝ := (I : ℝ) * (2 * Q)
  have hr : r ≤ 8 := (units_rank_le_finrank K).trans hdeg
  have hfac : (r.factorial : ℝ) ≤ 40320 := by
    exact_mod_cast (Nat.factorial_le hr).trans_eq
      (by norm_num : Nat.factorial 8 = 40320)
  have hcoord0 : 0 ≤ coord := by dsimp [coord]; positivity
  have hIc : (I : ℝ) ≤ Ic := by exact_mod_cast hindex
  have hcoord : coord ≤ (Ic : ℝ) * (2 * Qc) := by
    dsimp [coord]
    exact mul_le_mul hIc (by nlinarith) (by positivity) (Nat.cast_nonneg _)
  have hbase1 : 1 ≤ base := by dsimp [base]; nlinarith [mul_nonneg (Nat.cast_nonneg Ic) hQc0]
  have hmax0 : 0 ≤ max common coord :=
    hcoord0.trans (le_max_right common coord)
  have hmax : max common coord ≤ base := by
    apply max_le
    · dsimp [base, common]
      linarith
    · dsimp [base]
      linarith
  have hpow : (max common coord) ^ r ≤ base ^ 8 :=
    (pow_le_pow_left₀ hmax0 hmax r).trans (pow_le_pow_right₀ hbase1 hr)
  have hnum : (r.factorial : ℝ) * (max common coord) ^ r ≤
      40320 * base ^ 8 :=
    mul_le_mul hfac hpow (pow_nonneg hmax0 _) (by norm_num)
  have hden := totallyRealDegreeEightUnitGap_pow_rank_lower K hdeg
  have hdpos : 0 < (1 / 264 : ℝ) ^ 8 := by positivity
  have hquot := div_le_div₀ (by positivity) hnum hdpos hden
  have hrewrite : 40320 * base ^ 8 / (1 / 264 : ℝ) ^ 8 =
      40320 * (264 : ℝ) ^ 8 * base ^ 8 := by norm_num; ring
  calc
    ((NumberField.Units.rank K).factorial *
        (max (BoundedUnits.commonBoundedUnitLogBound (K := K) B)
          ((I : ℝ) * (2 * Q))) ^ NumberField.Units.rank K) /
        (totallyRealDegreeEightUnitLogGap / 8) ^ NumberField.Units.rank K ≤
        40320 * base ^ 8 / (1 / 264 : ℝ) ^ 8 := by
          simpa [r, common, coord] using hquot
    _ = 40320 * (264 : ℝ) ^ 8 * base ^ 8 := hrewrite
    _ = 40320 * (264 : ℝ) ^ 8 *
        (1 + C + (Ic : ℝ) * (2 * Qc)) ^ 8 := rfl

lemma realPell_coefficientRealBound_le_control
    {K : Type*} [Field K] [NumberField K]
    {H J x B IU : ℕ} {Qres : ℝ}
    (hdeg : Module.finrank ℚ K ≤ 8)
    (hcommon : BoundedUnits.commonBoundedUnitLogBound (K := K) B ≤
      pellCommonUnitControl H)
    (hindex : IU ≤ pellIndexControl H)
    (hQ0 : 0 ≤ Qres)
    (hQ : Qres ≤ pellResidualControl H J x)
    (hx : 0 < x) :
    ((NumberField.Units.rank K).factorial *
        (max (BoundedUnits.commonBoundedUnitLogBound (K := K) B)
          ((IU : ℝ) * (2 * Qres))) ^ NumberField.Units.rank K) /
        (totallyRealDegreeEightUnitLogGap / 8) ^ NumberField.Units.rank K ≤
      pellCoefficientControl H J x := by
  simpa only [pellCoefficientControl, pellCoordinateBaseControl] using
    (boundedUnitCoordinateRealBound_le_control
      (K := K) (B := B) (I := IU) hdeg
      (pellCommonUnitControl_nonneg H) hcommon hindex hQ0 hQ
      (pellResidualControl_nonneg hx))

lemma realPell_absorptionRealBound_le_control
    {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    {H J B : ℕ} {QW : ℝ}
    (hdeg : Module.finrank ℚ K ≤ 8)
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B)
    (hcommon : BoundedUnits.commonBoundedUnitLogBound (K := K) B ≤
      pellCommonUnitControl H)
    (hindex : (BoundedUnits.boundedUnitSubgroup hB).index ≤
      pellIndexControl H)
    (hQ0 : 0 ≤ QW) (hQ : QW ≤ pellLeadingControl H J) :
    integerUnitAbsorptionRealBound K hB QW ≤
      pellAbsorptionCoefficientControl H J := by
  unfold integerUnitAbsorptionRealBound
  simpa only [pellAbsorptionCoefficientControl,
    pellAbsorptionCoordinateBaseControl] using
    (boundedUnitCoordinateRealBound_le_control
      (K := K) (B := B)
      (I := (BoundedUnits.boundedUnitSubgroup hB).index) hdeg
      (pellCommonUnitControl_nonneg H) hcommon hindex hQ0 hQ
      (pellLeadingControl_nonneg H J))

lemma max_one_ceil_le_real_control {A C : ℝ}
    (hA0 : 0 ≤ A) (hC0 : 0 ≤ C) (hAC : A ≤ C) :
    ((max 1 (Nat.ceil A) : ℕ) : ℝ) ≤ C + 2 := by
  rw [Nat.cast_max]
  apply max_le
  · norm_num
    linarith
  · have hceil : ((Nat.ceil A : ℕ) : ℝ) < A + 1 := by
      exact_mod_cast Nat.ceil_lt_add_one hA0
    linarith

lemma realPell_integerUnitAbsorptionNatBound_le_control
    {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    {H J x B Ba : ℕ} {QW : ℝ}
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B)
    (hreal : integerUnitAbsorptionRealBound K hB QW ≤
      pellAbsorptionCoefficientControl H J)
    (hI : (BoundedUnits.boundedUnitSubgroup hB).index ≤ pellIndexControl H)
    (hBa : (Ba : ℝ) ≤ pellCoefficientControl H J x + 2) :
    (integerUnitAbsorptionNatBound K hB QW Ba : ℝ) ≤
      pellUnitBoxControl H J x := by
  have hreal0 : 0 ≤ integerUnitAbsorptionRealBound K hB QW := by
    unfold integerUnitAbsorptionRealBound
    have hcommon0 := BoundedUnits.commonBoundedUnitLogBound_nonneg hB
    have hmax0 : 0 ≤ max
        (BoundedUnits.commonBoundedUnitLogBound (K := K) B)
        (((BoundedUnits.boundedUnitSubgroup hB).index : ℝ) * (2 * QW)) :=
      hcommon0.trans (le_max_left _ _)
    exact div_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hmax0 _))
      (pow_nonneg (div_nonneg totallyRealDegreeEightUnitLogGap_pos.le (by norm_num)) _)
  have hceil :
      ((Nat.ceil (integerUnitAbsorptionRealBound K hB QW) : ℕ) : ℝ) ≤
        pellAbsorptionCoefficientControl H J + 1 := by
    have hlt :
        ((Nat.ceil (integerUnitAbsorptionRealBound K hB QW) : ℕ) : ℝ) <
          integerUnitAbsorptionRealBound K hB QW + 1 := by
      exact_mod_cast Nat.ceil_lt_add_one hreal0
    linarith
  have hIR :
      ((BoundedUnits.boundedUnitSubgroup hB).index : ℝ) ≤
        pellIndexControl H := by exact_mod_cast hI
  unfold integerUnitAbsorptionNatBound pellUnitBoxControl
  push_cast
  have hmul :
      (2 : ℝ) * (BoundedUnits.boundedUnitSubgroup hB).index * Ba ≤
        2 * pellIndexControl H * (pellCoefficientControl H J x + 2) := by
    have htwI : (2 : ℝ) * (BoundedUnits.boundedUnitSubgroup hB).index ≤
        2 * pellIndexControl H :=
      mul_le_mul_of_nonneg_left hIR (by norm_num)
    exact mul_le_mul htwI hBa (Nat.cast_nonneg _) (by positivity)
  linarith

lemma structuredBoxThresholdControl_le_of_bounds
    {F : Type*} [Field F] [NumberField F] {r : ℕ}
    (B : ℕ) (M LM BC Q : ℝ)
    (alpha : Fin (r + 1) → F) (ell : Fin (r + 1) → ℂ)
    (hlogM : Real.log M ≤ LM)
    (hBC0 : 0 ≤ BC) (hB : (B : ℝ) ≤ BC)
    (hheight : (∑ i, Height.logHeight₁ (alpha i)) ≤ Q)
    (hell : (∑ i, ‖ell i‖) ≤ ∑ i, Height.logHeight₁ (alpha i)) :
    LinearForms.structuredBoxThresholdControl B M alpha ell ≤
      (1000000000000000000000000000000 : ℝ) + LM +
        Real.log (2 * BC + 1) + 2 * Q := by
  have harg :
      (((2 * B + 1 : ℕ) : ℝ)) ≤ 2 * BC + 1 := by
    push_cast
    linarith
  have hargPos : (0 : ℝ) < ((2 * B + 1 : ℕ) : ℝ) := by positivity
  have hlogB : Real.log (((2 * B + 1 : ℕ) : ℝ)) ≤
      Real.log (2 * BC + 1) := Real.log_le_log hargPos harg
  unfold LinearForms.structuredBoxThresholdControl
  linarith

lemma pellCoefficientControl_nonneg {H J x : ℕ} (hx : 0 < x) :
    0 ≤ pellCoefficientControl H J x := by
  unfold pellCoefficientControl pellCoordinateBaseControl
  have hres := pellResidualControl_nonneg (H := H) (J := J) hx
  positivity

lemma pellAbsorptionCoefficientControl_nonneg (H J : ℕ) :
    0 ≤ pellAbsorptionCoefficientControl H J := by
  unfold pellAbsorptionCoefficientControl pellAbsorptionCoordinateBaseControl
  have hlead := pellLeadingControl_nonneg H J
  positivity

lemma pellUnitBoxControl_nonneg {H J x : ℕ} (hx : 0 < x) :
    0 ≤ pellUnitBoxControl H J x := by
  unfold pellUnitBoxControl
  have hcoef := pellCoefficientControl_nonneg (H := H) (J := J) hx
  have habs := pellAbsorptionCoefficientControl_nonneg H J
  have hmul : 0 ≤ (2 * pellIndexControl H : ℝ) *
      (pellCoefficientControl H J x + 2) :=
    mul_nonneg
      (mul_nonneg (by norm_num) (by exact_mod_cast (Nat.zero_le (pellIndexControl H))))
      (by linarith)
  linarith

lemma log_nat_cube_le_three_log_succ (H : ℕ) :
    Real.log ((H : ℝ) ^ 3) ≤ 3 * Real.log (H + 1 : ℕ) := by
  by_cases hH0 : H = 0
  · subst H
    simp
  · rw [Real.log_pow]
    have hlog : Real.log (H : ℝ) ≤ Real.log (H + 1 : ℕ) :=
      Real.log_le_log (by exact_mod_cast (show 0 < H by omega))
        (by exact_mod_cast (show H ≤ H + 1 by omega))
    simpa only [Nat.cast_ofNat] using
      (mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 3))

lemma realPell_nonunitThresholdControl_le
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {H J x B Ba : ℕ} {QW : ℝ}
    (hdeg : Module.finrank ℚ K ≤ 8)
    (hBcut : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B)
    (hcommon : BoundedUnits.commonBoundedUnitLogBound (K := K) B ≤
      pellCommonUnitControl H)
    (hBa : (Ba : ℝ) ≤ pellCoefficientControl H J x + 2)
    (hQW : QW ≤ pellLeadingControl H J)
    (φ : K →+* ℂ) (ρ : K →+* ℝ) (hφρ : ∀ z, φ z = (ρ z : ℂ))
    (W : K) (eps : Fin (NumberField.Units.rank K) → K)
    (hWheight : Height.logHeight₁ W ≤ QW)
    (heps : ∀ i, Height.logHeight₁ (eps i) ≤
      8 * BoundedUnits.commonBoundedUnitLogBound (K := K) B)
    (hpos : ∀ i, 0 < ρ (combinedSquaredProductBases W eps i))
    (hx : 0 < x) :
    let alpha := combinedSquaredProductBases W eps
    let ell : Fin (NumberField.Units.rank K + 1) → ℂ := fun i ↦
      Complex.log (φ (alpha i))
    LinearForms.structuredBoxThresholdControl Ba ((H : ℝ) ^ 3) alpha ell ≤
      pellThresholdControl H J x := by
  dsimp only
  let alpha := combinedSquaredProductBases W eps
  have hheight : (∑ i, Height.logHeight₁ (alpha i)) ≤
      pellLeadingControl H J + 128 * pellCommonUnitControl H := by
    have hsum := combinedSquaredProductBases_sum_logHeight_le W eps hWheight heps
    have hr : (NumberField.Units.rank K : ℝ) ≤ 8 := by
      exact_mod_cast (units_rank_le_finrank K).trans hdeg
    have hcommon0 := BoundedUnits.commonBoundedUnitLogBound_nonneg hBcut
    dsimp [alpha]
    calc
      (∑ i, Height.logHeight₁ (combinedSquaredProductBases W eps i)) ≤
          QW + (NumberField.Units.rank K : ℝ) *
            (2 * (8 * BoundedUnits.commonBoundedUnitLogBound (K := K) B)) := hsum
      _ ≤ pellLeadingControl H J + 128 * pellCommonUnitControl H := by
        nlinarith
  have hell : (∑ i, ‖Complex.log (φ (alpha i))‖) ≤
      ∑ i, Height.logHeight₁ (alpha i) :=
    sum_norm_complexLog_le_sum_logHeight_of_positive φ ρ hφρ alpha hpos
  have hraw := structuredBoxThresholdControl_le_of_bounds Ba ((H : ℝ) ^ 3)
    (3 * Real.log (H + 1 : ℕ)) (pellCoefficientControl H J x + 2)
    (pellLeadingControl H J + 128 * pellCommonUnitControl H)
    alpha (fun i ↦ Complex.log (φ (alpha i)))
    (log_nat_cube_le_three_log_succ H)
    (by nlinarith [pellCoefficientControl_nonneg (H := H) (J := J) hx])
    hBa hheight hell
  unfold pellThresholdControl
  have hlogUnit : 0 ≤ Real.log (2 * pellUnitBoxControl H J x + 3) := by
    exact Real.log_nonneg (by nlinarith [pellUnitBoxControl_nonneg (H := H) (J := J) hx])
  rw [show 2 * (pellCoefficientControl H J x + 2) + 1 =
      2 * pellCoefficientControl H J x + 5 by ring] at hraw
  exact hraw.trans (by linarith)

lemma realPell_unitThresholdControl_le
    {K : Type*} [Field K] [NumberField K]
    {H J x Bunit : ℕ}
    {αbase : Fin (NumberField.Units.rank K) → K}
    (φ : K →+* ℂ) (ρ : K →+* ℝ) (hφρ : ∀ z, φ z = (ρ z : ℂ))
    (reindex : Fin (NumberField.Units.rank K - 1 + 1) ≃
      Fin (NumberField.Units.rank K))
    (hBunit : (Bunit : ℝ) ≤ pellUnitBoxControl H J x)
    (hheightBase : (∑ i, Height.logHeight₁ (αbase i)) ≤
      128 * pellCommonUnitControl H)
    (hpos : ∀ i, 0 < ρ (αbase (reindex i)))
    (hx : 0 < x) :
    let alpha : Fin (NumberField.Units.rank K - 1 + 1) → K :=
      fun i ↦ αbase (reindex i)
    let ell : Fin (NumberField.Units.rank K - 1 + 1) → ℂ := fun i ↦
      Complex.log (φ (alpha i))
    LinearForms.structuredBoxThresholdControl Bunit ((H : ℝ) ^ 3) alpha ell ≤
      pellThresholdControl H J x := by
  dsimp only
  let alpha : Fin (NumberField.Units.rank K - 1 + 1) → K :=
    fun i ↦ αbase (reindex i)
  have hheight : (∑ i, Height.logHeight₁ (alpha i)) ≤
      128 * pellCommonUnitControl H := by
    calc
      (∑ i, Height.logHeight₁ (alpha i)) =
          ∑ j, Height.logHeight₁ (αbase j) := by
        exact reindex.sum_comp (fun j ↦ Height.logHeight₁ (αbase j))
      _ ≤ 128 * pellCommonUnitControl H := hheightBase
  have hell : (∑ i, ‖Complex.log (φ (alpha i))‖) ≤
      ∑ i, Height.logHeight₁ (alpha i) :=
    sum_norm_complexLog_le_sum_logHeight_of_positive φ ρ hφρ alpha hpos
  have hBunit' : (Bunit : ℝ) ≤ pellUnitBoxControl H J x + 1 := by linarith
  have hraw := structuredBoxThresholdControl_le_of_bounds Bunit ((H : ℝ) ^ 3)
    (3 * Real.log (H + 1 : ℕ)) (pellUnitBoxControl H J x + 1)
    (128 * pellCommonUnitControl H)
    alpha (fun i ↦ Complex.log (φ (alpha i)))
    (log_nat_cube_le_three_log_succ H)
    (by nlinarith [pellUnitBoxControl_nonneg (H := H) (J := J) hx])
    hBunit' hheight hell
  rw [show 2 * (pellUnitBoxControl H J x + 1) + 1 =
      2 * pellUnitBoxControl H J x + 3 by ring] at hraw
  unfold pellThresholdControl
  have hlogCoef : 0 ≤ Real.log (2 * pellCoefficientControl H J x + 5) := by
    exact Real.log_nonneg (by nlinarith
      [pellCoefficientControl_nonneg (H := H) (J := J) hx])
  have hlead := pellLeadingControl_nonneg H J
  exact hraw.trans (by linarith)

noncomputable def pellExponentControl (H : ℕ) : ℝ :=
  2 * pellClassControl H * pellIndexControl H +
    4 * pellClassControl H * (pellIndexControl H : ℝ) ^ 2

lemma pellExponentControl_nonneg (H : ℕ) : 0 ≤ pellExponentControl H := by
  unfold pellExponentControl
  have hc := pellClassControl_nonneg H
  have hi : 0 ≤ (pellIndexControl H : ℝ) := Nat.cast_nonneg _
  exact add_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) hc) hi)
    (mul_nonneg (mul_nonneg (by norm_num) hc) (sq_nonneg _))

lemma realPell_nonunitExponent_le_control
    {K : Type*} [Field K] [NumberField K] {H I : ℕ}
    (hclass : (NumberField.classNumber K : ℝ) ≤ pellClassControl H)
    (hI : I ≤ pellIndexControl H) :
    (((NumberField.classNumber K * I) * 2 : ℕ) : ℝ) ≤
      pellExponentControl H := by
  have hIR : (I : ℝ) ≤ pellIndexControl H := by exact_mod_cast hI
  have hclass0 : 0 ≤ (NumberField.classNumber K : ℝ) := by exact_mod_cast Nat.zero_le _
  have hprod : (NumberField.classNumber K : ℝ) * I ≤
      pellClassControl H * pellIndexControl H :=
    mul_le_mul hclass hIR (Nat.cast_nonneg _) (pellClassControl_nonneg H)
  have hsecond : 0 ≤ 4 * pellClassControl H *
      (pellIndexControl H : ℝ) ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) (pellClassControl_nonneg H)) (sq_nonneg _)
  calc
    (((NumberField.classNumber K * I) * 2 : ℕ) : ℝ) =
        2 * ((NumberField.classNumber K : ℝ) * I) := by push_cast; ring
    _ ≤ 2 * (pellClassControl H * pellIndexControl H) :=
      mul_le_mul_of_nonneg_left hprod (by norm_num)
    _ ≤ 2 * pellClassControl H * pellIndexControl H +
        4 * pellClassControl H * (pellIndexControl H : ℝ) ^ 2 := by
      simpa only [mul_assoc] using
        (le_add_of_nonneg_right hsecond :
          2 * pellClassControl H * pellIndexControl H ≤
            2 * pellClassControl H * pellIndexControl H +
              4 * pellClassControl H * (pellIndexControl H : ℝ) ^ 2)
    _ = pellExponentControl H := rfl

lemma realPell_unitExponent_le_control
    {K : Type*} [Field K] [NumberField K] {H I : ℕ}
    (hclass : (NumberField.classNumber K : ℝ) ≤ pellClassControl H)
    (hI : I ≤ pellIndexControl H) :
    ((((NumberField.classNumber K * I) * 2) * (2 * I) : ℕ) : ℝ) ≤
      pellExponentControl H := by
  have hIR : (I : ℝ) ≤ pellIndexControl H := by exact_mod_cast hI
  have hclass0 : 0 ≤ (NumberField.classNumber K : ℝ) := by exact_mod_cast Nat.zero_le _
  have hI0 : 0 ≤ (I : ℝ) := Nat.cast_nonneg _
  have hprod : (NumberField.classNumber K : ℝ) * I ^ 2 ≤
      pellClassControl H * (pellIndexControl H : ℝ) ^ 2 := by
    have hIsq := pow_le_pow_left₀ hI0 hIR 2
    exact mul_le_mul hclass hIsq (sq_nonneg _) (pellClassControl_nonneg H)
  have hfirst : 0 ≤ 2 * pellClassControl H * pellIndexControl H :=
    mul_nonneg (mul_nonneg (by norm_num) (pellClassControl_nonneg H))
      (Nat.cast_nonneg _)
  calc
    ((((NumberField.classNumber K * I) * 2) * (2 * I) : ℕ) : ℝ) =
        4 * ((NumberField.classNumber K : ℝ) * I ^ 2) := by push_cast; ring
    _ ≤ 4 * (pellClassControl H * (pellIndexControl H : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hprod (by norm_num)
    _ ≤ 2 * pellClassControl H * pellIndexControl H +
        4 * pellClassControl H * (pellIndexControl H : ℝ) ^ 2 := by
      simpa only [mul_assoc] using
        (le_add_of_nonneg_left hfirst :
          4 * pellClassControl H * (pellIndexControl H : ℝ) ^ 2 ≤
            2 * pellClassControl H * pellIndexControl H +
              4 * pellClassControl H * (pellIndexControl H : ℝ) ^ 2)
    _ = pellExponentControl H := rfl

lemma structuredBoxLogarithmicFormThreshold_lower_of_control
    {F : Type*} [Field F] [NumberField F] {r : ℕ}
    (B : ℕ) (M C : ℝ) (alpha : Fin (r + 1) → F)
    (ell : Fin (r + 1) → ℂ) (hM : 1 ≤ M)
    (hcontrol : LinearForms.structuredBoxThresholdControl B M alpha ell ≤ C) :
    Real.exp (-(3 * C ^ 9900)) ≤
      LinearForms.structuredBoxLogarithmicFormThreshold B
        (LinearForms.structuredBoxMasterL B M alpha ell) M alpha ell := by
  let T := LinearForms.structuredBoxThresholdControl B M alpha ell
  have hbase := LinearForms.structuredBoxLogarithmicFormThreshold_at_master_lower
    B M alpha ell hM
  have hTone : (1 : ℝ) ≤ T :=
    (LinearForms.structuredBoxMasterL_control_bound B M alpha ell hM).1
  have hpow : T ^ 9900 ≤ C ^ 9900 := by
    exact pow_le_pow_left₀ (by linarith) hcontrol _
  have hbase' : Real.exp (-(3 * T ^ 9900)) ≤
      LinearForms.structuredBoxLogarithmicFormThreshold B
        (LinearForms.structuredBoxMasterL B M alpha ell) M alpha ell := by
    simpa only [T] using hbase
  have hneg : -(3 * C ^ 9900) ≤ -(3 * T ^ 9900) := by nlinarith
  exact (Real.exp_le_exp.mpr hneg).trans hbase'

noncomputable def realPellApproximation
    (γ₁ γ₂ γ₃ x₁ x₂ x₃ : ℕ) (β₁₂ β₁₃ : ℤ) : ℝ :=
  (β₁₃ : ℝ) / (β₁₂ : ℝ) *
    ((Real.sqrt γ₁ * x₁ - Real.sqrt γ₂ * x₂) /
      (Real.sqrt γ₁ * x₁ - Real.sqrt γ₃ * x₃))

theorem realPell_uniform_logarithmic_form_lower
    {γ₁ γ₂ γ₃ H x₁ x₂ x₃ J : ℕ} {β₁₂ β₁₃ : ℤ}
    (hPell : SimultaneousPellZ (γ₁ : ℤ) (γ₂ : ℤ) (γ₃ : ℤ)
      β₁₂ β₁₃ (x₁ : ℤ) (x₂ : ℤ) (x₃ : ℤ))
    (hβ₁₂ : β₁₂ ≠ 0) (hβ₁₃ : β₁₃ ≠ 0)
    (hβ₂₃ : β₁₃ - β₁₂ ≠ 0)
    (hJ₁₂ : β₁₂.natAbs ≤ J) (hJ₁₃ : β₁₃.natAbs ≤ J)
    (hJ₂₃ : (β₁₃ - β₁₂).natAbs ≤ J)
    (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂) (hγ₃ : 0 < γ₃)
    (hγ₁H : γ₁ ≤ H) (hγ₂H : γ₂ ≤ H) (hγ₃H : γ₃ ≤ H)
    (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) (hx₃ : 0 < x₃)
    (hlarge : 2 * J < γ₁ * x₁ ^ 2) :
    ∃ k : ℕ, 0 < k ∧ (k : ℝ) ≤ pellExponentControl H ∧
      Real.exp (-(3 * pellThresholdControl H J x₁ ^ 9900)) ≤
        |Real.log ((realPellApproximation γ₁ γ₂ γ₃ x₁ x₂ x₃ β₁₂ β₁₃) ^ k)| ∧
      realPellApproximation γ₁ γ₂ γ₃ x₁ x₂ x₃ β₁₂ β₁₃ ≠ 1 ∧
      |realPellApproximation γ₁ γ₂ γ₃ x₁ x₂ x₃ β₁₂ β₁₃ - 1| ≤
        2 * (J : ℝ) / (Real.sqrt γ₁ * x₁) ^ 2 := by
  let K := realPellField γ₁ γ₂ γ₃
  let : Algebra ℚ K := K.algebra'
  let : NumberField K := realPellFieldNumberField γ₁ γ₂ γ₃
  let : NumberField.IsTotallyReal K := realPellFieldIsTotallyReal hγ₁ hγ₂ hγ₃
  let ratio : Kˣ :=
    Units.mk0 (β₁₃ : K) (Int.cast_ne_zero.mpr hβ₁₃) /
      Units.mk0 (β₁₂ : K) (Int.cast_ne_zero.mpr hβ₁₂)
  let N : ℕ := (40320 * H ^ 24) ^ 2
  let B : ℕ := degreeEightMinkowskiNatBound N
  have hdeg : Module.finrank ℚ K ≤ 8 := by
    change Module.finrank ℚ
      (IntermediateField.adjoin ℚ
        ({Real.sqrt γ₁, Real.sqrt γ₂, Real.sqrt γ₃} : Set ℝ)) ≤ 8
    exact finrank_adjoin_three_sqRoots_le_eight
      (Real.sqrt γ₁) (Real.sqrt γ₂) (Real.sqrt γ₃)
      (γ₁ : ℚ) (γ₂ : ℚ) (γ₃ : ℚ)
      (by simpa using Real.sq_sqrt (show (0 : ℝ) ≤ γ₁ by positivity))
      (by simpa using Real.sq_sqrt (show (0 : ℝ) ≤ γ₂ by positivity))
      (by simpa using Real.sq_sqrt (show (0 : ℝ) ≤ γ₃ by positivity))
  have hdata := realPell_controlled_archimedean_data hPell hβ₁₂ hβ₁₃ hβ₂₃
    hJ₁₂ hJ₁₃ hJ₂₃ hγ₁ hγ₂ hγ₃ hγ₁H hγ₂H hγ₃H
    hx₁ hx₂ hx₃ hlarge
  unfold RealPellControlledArchimedeanData at hdata
  dsimp only at hdata
  obtain ⟨S, U, hS, ι, hι, basis, e, q, hB, ζ, a,
      hSdef, hU, hgapNe, hgapAbs, hpow, he, hcoordE, hSJ,
      hindex, hdecomp, ha, hPheight, hWheight, hbasis, hMbasis, hdich⟩ := hdata
  let : Fintype S := hS.fintype
  let : Fintype ι := hι.fintype
  let I := (BoundedUnits.boundedUnitSubgroup hB).index
  let P : Kˣ := test_numberFieldPrimeClassBoundedSupportedUnitProduct hB S e
  let QP : ℝ := ((Fintype.card S : ℝ) * (J ^ 16 : ℝ)) *
    test_boundedPrimeClassHeightMajorant K B J
  let Qres : ℝ := (NumberField.classNumber K : ℝ) *
    Height.logHeight₁ (((U : Kˣ) : K)) + QP
  let IU := BoundedUnits.boundedUnitIndexUpper (K := K)
    (totallyRealDegreeEightUnitLogGap / 8) B
  let Acoef : ℝ := ((NumberField.Units.rank K).factorial *
      (max (BoundedUnits.commonBoundedUnitLogBound (K := K) B)
        ((IU : ℝ) * (2 * Qres))) ^ NumberField.Units.rank K) /
      (totallyRealDegreeEightUnitLogGap / 8) ^ NumberField.Units.rank K
  let Ba := max 1 (Nat.ceil Acoef)
  let QW : ℝ := (2 * (NumberField.classNumber K * I) : ℕ) *
      Height.logHeight₁ (ratio : K) + (2 * I : ℕ) * QP
  have hBH : B ≤ pellMinkowskiControl H := by
    simpa [B, N] using degreeEightMinkowskiNatBound_le_pellMinkowskiControl H
  have hclass : (NumberField.classNumber K : ℝ) ≤ pellClassControl H := by
    simpa [K] using realPellField_classNumber_le_control
      hγ₁ hγ₂ hγ₃ hγ₁H hγ₂H hγ₃H
  have hcommon := realPell_commonBoundedUnitLogBound_le_control hdeg hB hBH
  have hIU : IU ≤ pellIndexControl H := by
    exact realPell_boundedUnitIndexUpper_le_control hdeg hB hBH
  have hI : I ≤ pellIndexControl H := hindex.trans hIU
  have hcard : (Fintype.card S : ℝ) ≤ pellSupportControl J := by
    rw [← Nat.card_eq_fintype_card]
    rw [hSdef]
    exact pellCommonPrimeSupport_card_le_control hβ₁₂ hβ₁₃ hβ₂₃
      hJ₁₂ hJ₁₃ hJ₂₃ hdeg
  have hQP : QP ≤ pellPrimeProductControl H J := by
    exact realPell_primeProductHeightMajorant_le_control hdeg hB hBH hclass hcard
  have hJ : 1 ≤ J := (Int.natAbs_pos.mpr hβ₁₂).trans_le hJ₁₂
  have hQP0 : 0 ≤ QP := by
    dsimp [QP]
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _))
      (test_boundedPrimeClassHeightMajorant_nonneg K B hJ hB)
  have hUheight : Height.logHeight₁ (((U : Kˣ) : K)) ≤
      pellLeftUnitControl H J x₁ := by
    rw [hU]
    exact realPell_leftUnit_logHeight_le_coarse
      (realPellRootOne_sq γ₁ γ₂ γ₃)
      (realPellRootTwo_sq γ₁ γ₂ γ₃)
      (realPellRootThree_sq γ₁ γ₂ γ₃)
      hPell hJ₁₂ hJ₁₃ hdeg hγ₁ hγ₂ hγ₃
      hγ₁H hγ₂H hγ₃H hx₁ hx₂ hx₃
  have hQres0 : 0 ≤ Qres := by
    dsimp [Qres]
    exact add_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (Height.zero_le_logHeight₁ _)) hQP0
  have hQres : Qres ≤ pellResidualControl H J x₁ := by
    dsimp [Qres, pellResidualControl]
    exact add_le_add
      (mul_le_mul hclass hUheight (Height.zero_le_logHeight₁ _)
        (pellClassControl_nonneg H)) hQP
  have hAcoef : Acoef ≤ pellCoefficientControl H J x₁ := by
    exact realPell_coefficientRealBound_le_control hdeg hcommon hIU hQres0 hQres hx₁
  have hAcoef0 : 0 ≤ Acoef := by
    dsimp [Acoef]
    have hc0 := BoundedUnits.commonBoundedUnitLogBound_nonneg hB
    have hm0 : 0 ≤ max (BoundedUnits.commonBoundedUnitLogBound (K := K) B)
        ((IU : ℝ) * (2 * Qres)) := hc0.trans (le_max_left _ _)
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hm0 _))
      (pow_nonneg (div_pos totallyRealDegreeEightUnitLogGap_pos (by norm_num)).le _)
  have hBa : (Ba : ℝ) ≤ pellCoefficientControl H J x₁ + 2 := by
    exact max_one_ceil_le_real_control hAcoef0
      (pellCoefficientControl_nonneg (H := H) (J := J) hx₁) hAcoef
  have hratio : Height.logHeight₁ (ratio : K) ≤ pellRatioControl J := by
    simpa [ratio] using realPell_ratioHeight_le_control (K := K)
      hβ₁₃ hβ₁₂ hJ₁₃ hJ₁₂ hdeg
  have hQW0 : 0 ≤ QW := by
    dsimp [QW]
    exact add_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (Height.zero_le_logHeight₁ _))
      (mul_nonneg (Nat.cast_nonneg _) hQP0)
  have hQW : QW ≤ pellLeadingControl H J := by
    have hfirst :
        (2 * (NumberField.classNumber K * I) : ℕ) *
            Height.logHeight₁ (ratio : K) + (2 * I : ℕ) * QP ≤
          (2 * (NumberField.classNumber K * I) : ℕ) *
            pellRatioControl J + (2 * I : ℕ) * QP :=
      add_le_add
        (mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg _))
        (le_refl _)
    have hsecond := realPell_leadingHeightMajorant_le_control
      (K := K) (H := H) (J := J) (I := I) (QP := QP)
      hclass hI hQP0 hQP
    exact hfirst.trans hsecond
  have habsReal := realPell_absorptionRealBound_le_control hdeg hB hcommon hI hQW0 hQW
  have habsNat :
      (integerUnitAbsorptionNatBound K hB QW Ba : ℝ) ≤
        pellUnitBoxControl H J x₁ :=
    realPell_integerUnitAbsorptionNatBound_le_control hB habsReal hI hBa
  let eps : Fin (NumberField.Units.rank K) → K := fun i ↦
    ((Units.map (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom
      (BoundedUnits.boundedFundSystem hB i) : Kˣ) : K)
  let W : Kˣ := (ratio ^ 2) ^ (NumberField.classNumber K * I) * (P ^ 2) ^ I
  let z : K := ((ratio * (U : Kˣ) : Kˣ) : K)
  let m := (NumberField.classNumber K * I) * 2
  have hzapprox : realPellRealEmbedding γ₁ γ₂ γ₃ z =
      realPellApproximation γ₁ γ₂ γ₃ x₁ x₂ x₃ β₁₂ β₁₃ := by
    dsimp [z, ratio, realPellApproximation]
    rw [hU]
    simp [realPellRealEmbedding, realPellRootOne, realPellRootTwo,
      realPellRootThree, pellValueMinus]
  have hMapPow (k : ℕ) : realPellRealEmbedding γ₁ γ₂ γ₃ (z ^ k) =
      (realPellApproximation γ₁ γ₂ γ₃ x₁ x₂ x₃ β₁₂ β₁₃) ^ k := by
    rw [map_pow, hzapprox]
  have hM : (1 : ℝ) ≤ (H : ℝ) ^ 3 := by
    exact one_le_pow₀ (by exact_mod_cast hγ₁.trans_le hγ₁H)
  have hdich' : SupportedUnitControlledCombinedRealLogDichotomy basis
      (realPellComplexEmbedding γ₁ γ₂ γ₃)
      (realPellRealEmbedding γ₁ γ₂ γ₃) U ratio P hB a Ba QW
      ((H : ℝ) ^ 3) := by
    simpa [K, N, B, ratio, I, P, QP, Qres, IU, Acoef, Ba, QW] using hdich
  unfold SupportedUnitControlledCombinedRealLogDichotomy at hdich'
  dsimp only at hdich'
  rcases hdich' with hnon | hunit
  · rcases hnon with ⟨_hWnon, hlower⟩
    let alpha := combinedSquaredProductBases (W : K) eps
    let ell : Fin (NumberField.Units.rank K + 1) → ℂ := fun i ↦
      Complex.log (realPellComplexEmbedding γ₁ γ₂ γ₃ (alpha i))
    have hWpos : 0 < realPellRealEmbedding γ₁ γ₂ γ₃ (W : K) :=
      combinedLeadingFactor_positive (realPellRealEmbedding γ₁ γ₂ γ₃)
        (ratio : K) (P : K) (NumberField.classNumber K) I
        (Units.ne_zero ratio) (Units.ne_zero P)
    have hepsHeight : ∀ i, Height.logHeight₁ (eps i) ≤
        8 * BoundedUnits.commonBoundedUnitLogBound (K := K) B := by
      intro i
      simpa [eps] using boundedFundSystem_logHeight_le_degree_eight K hdeg hB i
    have hpos := combinedSquaredProductBases_positive
      (realPellRealEmbedding γ₁ γ₂ γ₃) hWpos eps (fun i ↦ by
        change (((Units.map
          (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom
            (BoundedUnits.boundedFundSystem hB i) : Kˣ) : K)) ≠ 0
        exact Units.ne_zero _)
    have hcontrol : LinearForms.structuredBoxThresholdControl Ba ((H : ℝ) ^ 3)
        alpha ell ≤ pellThresholdControl H J x₁ := by
      exact realPell_nonunitThresholdControl_le hdeg hB hcommon hBa hQW
        (realPellComplexEmbedding γ₁ γ₂ γ₃)
        (realPellRealEmbedding γ₁ γ₂ γ₃) (fun _ ↦ rfl)
        (W : K) eps hWheight hepsHeight hpos hx₁
    have hmaster := structuredBoxLogarithmicFormThreshold_lower_of_control
      Ba ((H : ℝ) ^ 3) (pellThresholdControl H J x₁) alpha ell hM hcontrol
    refine ⟨m, ?_, realPell_nonunitExponent_le_control hclass hI, ?_, ?_, ?_⟩
    · dsimp [m, I]
      exact Nat.mul_pos (Nat.mul_pos (NumberField.classNumber_pos K)
        (Nat.pos_of_ne_zero (BoundedUnits.boundedUnitSubgroup_index_ne_zero hB)))
        (by norm_num)
    · rw [← hMapPow m]
      exact hmaster.trans (by
        simpa [alpha, ell, W, z, m, eps] using hlower)
    · rw [← hzapprox]
      exact fun h ↦ hgapNe (sub_eq_zero.mpr h)
    · rw [← hzapprox]
      exact hgapAbs

  · rcases hunit with ⟨c, reindex, _hWunit, hlower⟩
    let alphaBase : Fin (NumberField.Units.rank K) → K := fun i ↦ eps i ^ 2
    let alpha : Fin (NumberField.Units.rank K - 1 + 1) → K :=
      fun i ↦ alphaBase (reindex i)
    let ell : Fin (NumberField.Units.rank K - 1 + 1) → ℂ := fun i ↦
      Complex.log (realPellComplexEmbedding γ₁ γ₂ γ₃ (alpha i))
    have hheightBase : (∑ i, Height.logHeight₁ (alphaBase i)) ≤
        128 * pellCommonUnitControl H := by
      exact (boundedUnitSquares_sum_logHeight_le hdeg hB).trans
        (mul_le_mul_of_nonneg_left hcommon (by norm_num))
    have hpos : ∀ i, 0 < realPellRealEmbedding γ₁ γ₂ γ₃
        (alphaBase (reindex i)) := by
      intro i
      dsimp [alphaBase]
      rw [map_pow]
      apply sq_pos_of_ne_zero
      apply (map_ne_zero _).2
      change (((Units.map
        (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom
          (BoundedUnits.boundedFundSystem hB (reindex i)) : Kˣ) : K)) ≠ 0
      exact Units.ne_zero _
    have hcontrol : LinearForms.structuredBoxThresholdControl
        (integerUnitAbsorptionNatBound K hB QW Ba) ((H : ℝ) ^ 3)
        alpha ell ≤ pellThresholdControl H J x₁ := by
      exact realPell_unitThresholdControl_le
        (realPellComplexEmbedding γ₁ γ₂ γ₃)
        (realPellRealEmbedding γ₁ γ₂ γ₃) (fun _ ↦ rfl)
        reindex habsNat hheightBase hpos hx₁
    have hmaster := structuredBoxLogarithmicFormThreshold_lower_of_control
      (integerUnitAbsorptionNatBound K hB QW Ba) ((H : ℝ) ^ 3)
      (pellThresholdControl H J x₁) alpha ell hM hcontrol
    let k := m * (2 * I)
    refine ⟨k, ?_, realPell_unitExponent_le_control hclass hI, ?_, ?_, ?_⟩
    · dsimp [k, m, I]
      exact Nat.mul_pos
        (Nat.mul_pos (Nat.mul_pos (NumberField.classNumber_pos K)
          (Nat.pos_of_ne_zero (BoundedUnits.boundedUnitSubgroup_index_ne_zero hB)))
          (by norm_num))
        (Nat.mul_pos (by norm_num)
          (Nat.pos_of_ne_zero (BoundedUnits.boundedUnitSubgroup_index_ne_zero hB)))
    · rw [← hMapPow k]
      have hlower' :
          LinearForms.structuredBoxLogarithmicFormThreshold
              (integerUnitAbsorptionNatBound K hB QW Ba)
              (LinearForms.structuredBoxMasterL
                (integerUnitAbsorptionNatBound K hB QW Ba) ((H : ℝ) ^ 3)
                alpha ell) ((H : ℝ) ^ 3) alpha ell ≤
            ((2 * I : ℕ) : ℝ) *
              ((m : ℝ) * |Real.log (realPellRealEmbedding γ₁ γ₂ γ₃ z)|) := by
        simpa [K, alpha, alphaBase, ell, eps, z, m] using hlower
      calc
        Real.exp (-(3 * pellThresholdControl H J x₁ ^ 9900)) ≤
            LinearForms.structuredBoxLogarithmicFormThreshold
              (integerUnitAbsorptionNatBound K hB QW Ba)
              (LinearForms.structuredBoxMasterL
                (integerUnitAbsorptionNatBound K hB QW Ba) ((H : ℝ) ^ 3)
                alpha ell) ((H : ℝ) ^ 3) alpha ell := hmaster
        _ ≤ ((2 * I : ℕ) : ℝ) *
              ((m : ℝ) * |Real.log (realPellRealEmbedding γ₁ γ₂ γ₃ z)|) := hlower'
        _ = |Real.log (realPellRealEmbedding γ₁ γ₂ γ₃ (z ^ k))| := by
          rw [map_pow, Real.log_pow, abs_mul]
          have habsk : |(k : ℝ)| = (k : ℝ) := abs_of_nonneg (Nat.cast_nonneg k)
          rw [habsk]
          have hkcast : (k : ℝ) = (m : ℝ) * ((2 * I : ℕ) : ℝ) := by
            exact_mod_cast (show k = m * (2 * I) by rfl)
          rw [hkcast]
          ring
    · rw [← hzapprox]
      exact fun h ↦ hgapNe (sub_eq_zero.mpr h)
    · rw [← hzapprox]
      exact hgapAbs

theorem realPell_uniform_log_coordinate_inequality
    {γ₁ γ₂ γ₃ H x₁ x₂ x₃ J : ℕ} {β₁₂ β₁₃ : ℤ}
    (hPell : SimultaneousPellZ (γ₁ : ℤ) (γ₂ : ℤ) (γ₃ : ℤ)
      β₁₂ β₁₃ (x₁ : ℤ) (x₂ : ℤ) (x₃ : ℤ))
    (hβ₁₂ : β₁₂ ≠ 0) (hβ₁₃ : β₁₃ ≠ 0)
    (hβ₂₃ : β₁₃ - β₁₂ ≠ 0)
    (hJ₁₂ : β₁₂.natAbs ≤ J) (hJ₁₃ : β₁₃.natAbs ≤ J)
    (hJ₂₃ : (β₁₃ - β₁₂).natAbs ≤ J)
    (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂) (hγ₃ : 0 < γ₃)
    (hγ₁H : γ₁ ≤ H) (hγ₂H : γ₂ ≤ H) (hγ₃H : γ₃ ≤ H)
    (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) (hx₃ : 0 < x₃)
    (hlarge : 4 * J < γ₁ * x₁ ^ 2) :
    2 * Real.log (x₁ : ℝ) ≤
      3 * pellThresholdControl H J x₁ ^ 9900 +
        Real.log (4 * pellExponentControl H * (J : ℝ)) := by
  have hlarge2 : 2 * J < γ₁ * x₁ ^ 2 := by omega
  obtain ⟨k, hk, hkE, hlower, hzNe, hgap⟩ :=
    realPell_uniform_logarithmic_form_lower hPell hβ₁₂ hβ₁₃ hβ₂₃
      hJ₁₂ hJ₁₃ hJ₂₃ hγ₁ hγ₂ hγ₃ hγ₁H hγ₂H hγ₃H
      hx₁ hx₂ hx₃ hlarge2
  let z := realPellApproximation γ₁ γ₂ γ₃ x₁ x₂ x₃ β₁₂ β₁₃
  let E := pellExponentControl H
  let T := pellThresholdControl H J x₁
  have hden : (Real.sqrt γ₁ * (x₁ : ℝ)) ^ 2 =
      (γ₁ : ℝ) * (x₁ : ℝ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hgapHalf : |z - 1| ≤ 1 / 2 := by
    have hlt : 2 * (J : ℝ) /
        (Real.sqrt γ₁ * (x₁ : ℝ)) ^ 2 < 1 / 2 := by
      rw [hden]
      have hlargeR : (4 : ℝ) * (J : ℝ) <
          (γ₁ : ℝ) * (x₁ : ℝ) ^ 2 := by
        exact_mod_cast hlarge
      apply (div_lt_iff₀ (by positivity)).2
      nlinarith
    have hgap' : |z - 1| ≤ 2 * (J : ℝ) /
        (Real.sqrt γ₁ * (x₁ : ℝ)) ^ 2 := by
      simpa [z] using hgap
    exact hgap'.trans hlt.le
  have hzpos : 0 < z := by
    have hzlower := (abs_le.mp hgapHalf).1
    linarith
  have hupper0 : |Real.log (z ^ k)| ≤ (2 * k : ℕ) * |z - 1| :=
    abs_log_pow_le_of_close hzpos hgapHalf k
  have hupper1 : |Real.log (z ^ k)| ≤
      ((2 * k : ℕ) : ℝ) *
        (2 * (J : ℝ) / ((γ₁ : ℝ) * (x₁ : ℝ) ^ 2)) := by
    refine hupper0.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
    rw [← hden]
    simpa [z] using hgap
  have hkRpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hEpos : 0 < E :=
    lt_of_lt_of_le hkRpos (by simpa [E] using hkE)
  have hJpos : 0 < (J : ℝ) := by
    exact_mod_cast (Int.natAbs_pos.mpr hβ₁₂).trans_le hJ₁₂
  have hγR : (1 : ℝ) ≤ γ₁ := by exact_mod_cast hγ₁
  have hxR : 0 < (x₁ : ℝ) := by exact_mod_cast hx₁
  have hupper2 : |Real.log (z ^ k)| ≤
      (4 * E * (J : ℝ)) / (x₁ : ℝ) ^ 2 := by
    refine hupper1.trans ?_
    have hkR : (k : ℝ) ≤ E := by simpa [E] using hkE
    calc
      (((2 * k : ℕ) : ℝ) *
          (2 * (J : ℝ) / ((γ₁ : ℝ) * (x₁ : ℝ) ^ 2))) =
          (4 * (k : ℝ) * (J : ℝ)) /
            ((γ₁ : ℝ) * (x₁ : ℝ) ^ 2) := by
              push_cast
              ring
      _ ≤ (4 * E * (J : ℝ)) /
            ((γ₁ : ℝ) * (x₁ : ℝ) ^ 2) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          calc
            4 * (k : ℝ) * (J : ℝ) = (k : ℝ) * (4 * (J : ℝ)) := by ring
            _ ≤ E * (4 * (J : ℝ)) :=
              mul_le_mul_of_nonneg_right hkR (by positivity)
            _ = 4 * E * (J : ℝ) := by ring
      _ ≤ (4 * E * (J : ℝ)) / (x₁ : ℝ) ^ 2 := by
          apply div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hxR)
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right hγR (sq_nonneg (x₁ : ℝ))
  have hlowup : Real.exp (-(3 * T ^ 9900)) ≤
      (4 * E * (J : ℝ)) / (x₁ : ℝ) ^ 2 := by
    have hlower' : Real.exp (-(3 * T ^ 9900)) ≤
        |Real.log (z ^ k)| := by
      simpa [z, T] using hlower
    exact hlower'.trans hupper2
  have hmul : Real.exp (-(3 * T ^ 9900)) * (x₁ : ℝ) ^ 2 ≤
      4 * E * (J : ℝ) := (le_div_iff₀ (sq_pos_of_pos hxR)).mp hlowup
  have hleftPos : 0 < Real.exp (-(3 * T ^ 9900)) * (x₁ : ℝ) ^ 2 := by positivity
  have hrightPos : 0 < 4 * E * (J : ℝ) := by positivity
  have hlog := Real.log_le_log hleftPos hmul
  rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt (sq_pos_of_pos hxR)),
    Real.log_exp, Real.log_pow] at hlog
  have hfinal :
      2 * Real.log (x₁ : ℝ) ≤ 3 * T ^ 9900 +
        Real.log (4 * E * (J : ℝ)) := by
    norm_num at hlog ⊢
    linarith
  simpa [T, E] using hfinal

noncomputable def pellResidualAffineControl (H J : ℕ) : ℝ :=
  pellClassControl H * 100 * (1 + Real.log (H + J + 1 : ℕ)) +
    pellPrimeProductControl H J + 100 * pellClassControl H

noncomputable def pellCoordinateStaticControl (H J : ℕ) : ℝ :=
  1 + pellCommonUnitControl H +
    (pellIndexControl H : ℝ) * (2 * pellResidualAffineControl H J)

noncomputable def pellCoefficientStaticControl (H J : ℕ) : ℝ :=
  40320 * (264 : ℝ) ^ 8 * pellCoordinateStaticControl H J ^ 8

noncomputable def pellUnitBoxStaticControl (H J : ℕ) : ℝ :=
  pellAbsorptionCoefficientControl H J + 1 +
    2 * pellIndexControl H * (pellCoefficientStaticControl H J + 2)

noncomputable def pellThresholdStaticControl (H J : ℕ) : ℝ :=
  (1000000000000000000000000000000 : ℝ) +
    3 * Real.log (H + 1 : ℕ) +
    Real.log (2 * pellCoefficientStaticControl H J + 5) +
    Real.log (2 * pellUnitBoxStaticControl H J + 3) +
    2 * (pellLeadingControl H J + 128 * pellCommonUnitControl H) + 16

lemma pellResidualAffineControl_nonneg (H J : ℕ) :
    0 ≤ pellResidualAffineControl H J := by
  unfold pellResidualAffineControl
  have hclass := pellClassControl_nonneg H
  have hprime := pellPrimeProductControl_nonneg H J
  have hlog : 0 ≤ Real.log (H + J + 1 : ℕ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ H + J + 1 by omega))
  positivity

lemma pellCoordinateStaticControl_pos (H J : ℕ) :
    0 < pellCoordinateStaticControl H J := by
  have hcommon := pellCommonUnitControl_nonneg H
  have hres := pellResidualAffineControl_nonneg H J
  have hI : 0 ≤ (pellIndexControl H : ℝ) := Nat.cast_nonneg _
  rw [pellCoordinateStaticControl]
  exact add_pos_of_pos_of_nonneg (by linarith)
    (mul_nonneg hI (mul_nonneg (by norm_num) hres))

lemma pellCoefficientStaticControl_pos (H J : ℕ) :
    0 < pellCoefficientStaticControl H J := by
  have hcoord := pellCoordinateStaticControl_pos H J
  rw [pellCoefficientStaticControl]
  exact mul_pos (mul_pos (by norm_num) (pow_pos (by norm_num) _))
    (pow_pos hcoord _)

lemma pellUnitBoxStaticControl_pos (H J : ℕ) :
    0 < pellUnitBoxStaticControl H J := by
  have habs := pellAbsorptionCoefficientControl_nonneg H J
  have hI : 0 ≤ (pellIndexControl H : ℝ) := Nat.cast_nonneg _
  have hcoef := pellCoefficientStaticControl_pos H J
  rw [pellUnitBoxStaticControl]
  have htail : 0 ≤ (2 : ℝ) * pellIndexControl H *
      (pellCoefficientStaticControl H J + 2) := by positivity
  linarith

lemma pellThresholdStaticControl_pos (H J : ℕ) :
    0 < pellThresholdStaticControl H J := by
  unfold pellThresholdStaticControl
  have hcoef := pellCoefficientStaticControl_pos H J
  have hunit := pellUnitBoxStaticControl_pos H J
  have hlead := pellLeadingControl_nonneg H J
  have hcommon := pellCommonUnitControl_nonneg H
  have hlogH : 0 ≤ Real.log (H + 1 : ℕ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ H + 1 by omega))
  have hlogCoef : 0 ≤ Real.log (2 * pellCoefficientStaticControl H J + 5) :=
    Real.log_nonneg (by nlinarith)
  have hlogUnit : 0 ≤ Real.log (2 * pellUnitBoxStaticControl H J + 3) :=
    Real.log_nonneg (by nlinarith)
  positivity

lemma pellResidualControl_le_affine
    {H J x : ℕ} (hx : 0 < x) :
    pellResidualControl H J x ≤ pellResidualAffineControl H J *
      (1 + Real.log (x : ℝ)) := by
  have hlogx : 0 ≤ Real.log (x : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hx)
  have hclass := pellClassControl_nonneg H
  have hprime := pellPrimeProductControl_nonneg H J
  have hlogHJ : 0 ≤ Real.log (H + J + 1 : ℕ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ H + J + 1 by omega))
  unfold pellResidualControl pellLeftUnitControl pellResidualAffineControl
  nlinarith [mul_nonneg hprime hlogx,
    mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 100) hclass) hlogx,
    mul_nonneg
      (mul_nonneg hclass (mul_nonneg (by norm_num : (0 : ℝ) ≤ 100)
        (by linarith : 0 ≤ 1 + Real.log (H + J + 1 : ℕ)))) hlogx]

lemma pellCoordinateBaseControl_le_static
    {H J x : ℕ} (hx : 0 < x) :
    pellCoordinateBaseControl H J x ≤ pellCoordinateStaticControl H J *
      (1 + Real.log (x : ℝ)) := by
  have hlogx : 0 ≤ Real.log (x : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hx)
  have hres := pellResidualControl_le_affine (H := H) (J := J) hx
  have hcommon := pellCommonUnitControl_nonneg H
  have hI : 0 ≤ (pellIndexControl H : ℝ) := Nat.cast_nonneg _
  have hstatic := pellResidualAffineControl_nonneg H J
  unfold pellCoordinateBaseControl pellCoordinateStaticControl
  nlinarith [mul_nonneg hcommon hlogx,
    mul_nonneg (mul_nonneg hI (by norm_num : (0 : ℝ) ≤ 2))
      (mul_nonneg hstatic hlogx),
    mul_nonneg (mul_nonneg hI (by norm_num : (0 : ℝ) ≤ 2))
      (sub_nonneg.mpr hres)]

lemma pellCoefficientControl_le_static
    {H J x : ℕ} (hx : 0 < x) :
    pellCoefficientControl H J x ≤ pellCoefficientStaticControl H J *
      (1 + Real.log (x : ℝ)) ^ 8 := by
  have hbase := pellCoordinateBaseControl_le_static (H := H) (J := J) hx
  have hbase0 : 0 ≤ pellCoordinateBaseControl H J x := by
    have hcommon := pellCommonUnitControl_nonneg H
    have hres := pellResidualControl_nonneg (H := H) (J := J) hx
    have hI : 0 ≤ (pellIndexControl H : ℝ) := Nat.cast_nonneg _
    rw [pellCoordinateBaseControl]
    exact add_nonneg (by linarith)
      (mul_nonneg hI (mul_nonneg (by norm_num) hres))
  have hpow := pow_le_pow_left₀ hbase0 hbase 8
  unfold pellCoefficientControl pellCoefficientStaticControl at *
  calc
    40320 * 264 ^ 8 * pellCoordinateBaseControl H J x ^ 8 ≤
        40320 * 264 ^ 8 *
          (pellCoordinateStaticControl H J * (1 + Real.log (x : ℝ))) ^ 8 :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = 40320 * 264 ^ 8 * pellCoordinateStaticControl H J ^ 8 *
        (1 + Real.log (x : ℝ)) ^ 8 := by ring

lemma pellUnitBoxControl_le_static
    {H J x : ℕ} (hx : 0 < x) :
    pellUnitBoxControl H J x ≤ pellUnitBoxStaticControl H J *
      (1 + Real.log (x : ℝ)) ^ 8 := by
  have hlogx : 0 ≤ Real.log (x : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hx)
  have hpow1 : (1 : ℝ) ≤ (1 + Real.log (x : ℝ)) ^ 8 :=
    one_le_pow₀ (by linarith)
  have hcoef := pellCoefficientControl_le_static (H := H) (J := J) hx
  have habs := pellAbsorptionCoefficientControl_nonneg H J
  have hI : 0 ≤ (pellIndexControl H : ℝ) := Nat.cast_nonneg _
  have hcoefStatic := pellCoefficientStaticControl_pos H J
  unfold pellUnitBoxControl pellUnitBoxStaticControl
  push_cast
  nlinarith [mul_nonneg habs (sub_nonneg.mpr hpow1),
    mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hI)
      (sub_nonneg.mpr hcoef),
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hI)
      (by norm_num : (0 : ℝ) ≤ 2)) (sub_nonneg.mpr hpow1),
    mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hI)
      (mul_nonneg hcoefStatic.le (sub_nonneg.mpr hpow1))]

lemma pellThresholdControl_le_static_mul_log
    {H J x : ℕ} (hx : 0 < x) :
    pellThresholdControl H J x ≤ pellThresholdStaticControl H J *
      (1 + Real.log (1 + Real.log (x : ℝ))) := by
  let Y := Real.log (x : ℝ)
  let P := (1 + Y) ^ 8
  have hY : 0 ≤ Y := by
    dsimp [Y]
    exact Real.log_nonneg (by exact_mod_cast hx)
  have hP1 : (1 : ℝ) ≤ P := by
    dsimp [P]
    exact one_le_pow₀ (by linarith)
  have hcoef := pellCoefficientControl_le_static (H := H) (J := J) hx
  have hunit := pellUnitBoxControl_le_static (H := H) (J := J) hx
  have hcoefArg : 2 * pellCoefficientControl H J x + 5 ≤
      (2 * pellCoefficientStaticControl H J + 5) * P := by
    dsimp [Y, P] at hcoef ⊢
    nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 5)
      (sub_nonneg.mpr hP1)]
  have hunitArg : 2 * pellUnitBoxControl H J x + 3 ≤
      (2 * pellUnitBoxStaticControl H J + 3) * P := by
    dsimp [Y, P] at hunit ⊢
    nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 3)
      (sub_nonneg.mpr hP1)]
  have hcoefLog : Real.log (2 * pellCoefficientControl H J x + 5) ≤
      Real.log (2 * pellCoefficientStaticControl H J + 5) +
        8 * Real.log (1 + Y) := by
    calc
      Real.log (2 * pellCoefficientControl H J x + 5) ≤
          Real.log ((2 * pellCoefficientStaticControl H J + 5) * P) :=
        Real.log_le_log (by
          nlinarith [pellCoefficientControl_nonneg (H := H) (J := J) hx]) hcoefArg
      _ = Real.log (2 * pellCoefficientStaticControl H J + 5) +
          Real.log P := by
        rw [Real.log_mul (by nlinarith [pellCoefficientStaticControl_pos H J])
          (by positivity : P ≠ 0)]
      _ = Real.log (2 * pellCoefficientStaticControl H J + 5) +
          8 * Real.log (1 + Y) := by
        dsimp [P]
        rw [Real.log_pow]
        norm_num
  have hunitLog : Real.log (2 * pellUnitBoxControl H J x + 3) ≤
      Real.log (2 * pellUnitBoxStaticControl H J + 3) +
        8 * Real.log (1 + Y) := by
    calc
      Real.log (2 * pellUnitBoxControl H J x + 3) ≤
          Real.log ((2 * pellUnitBoxStaticControl H J + 3) * P) :=
        Real.log_le_log (by
          nlinarith [pellUnitBoxControl_nonneg (H := H) (J := J) hx]) hunitArg
      _ = Real.log (2 * pellUnitBoxStaticControl H J + 3) +
          Real.log P := by
        rw [Real.log_mul (by nlinarith [pellUnitBoxStaticControl_pos H J])
          (by positivity : P ≠ 0)]
      _ = Real.log (2 * pellUnitBoxStaticControl H J + 3) +
          8 * Real.log (1 + Y) := by
        dsimp [P]
        rw [Real.log_pow]
        norm_num
  have hloglog : 0 ≤ Real.log (1 + Y) :=
    Real.log_nonneg (by linarith)
  have hstatic := pellThresholdStaticControl_pos H J
  have hstatic16 : (16 : ℝ) ≤ pellThresholdStaticControl H J := by
    rw [pellThresholdStaticControl]
    have hcoef := pellCoefficientStaticControl_pos H J
    have hunit := pellUnitBoxStaticControl_pos H J
    have hlead := pellLeadingControl_nonneg H J
    have hcommon := pellCommonUnitControl_nonneg H
    have hlogH : 0 ≤ Real.log (H + 1 : ℕ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ H + 1 by omega))
    have hlogCoef : 0 ≤ Real.log (2 * pellCoefficientStaticControl H J + 5) :=
      Real.log_nonneg (by nlinarith)
    have hlogUnit : 0 ≤ Real.log (2 * pellUnitBoxStaticControl H J + 3) :=
      Real.log_nonneg (by nlinarith)
    nlinarith
  have hraw : pellThresholdControl H J x ≤
      pellThresholdStaticControl H J - 16 +
        16 * Real.log (1 + Real.log (x : ℝ)) := by
    unfold pellThresholdControl pellThresholdStaticControl
    dsimp [Y] at hcoefLog hunitLog ⊢
    linarith
  calc
    pellThresholdControl H J x ≤ pellThresholdStaticControl H J - 16 +
        16 * Real.log (1 + Real.log (x : ℝ)) := hraw
    _ ≤ pellThresholdStaticControl H J *
        (1 + Real.log (1 + Real.log (x : ℝ))) := by
      dsimp [Y] at hloglog
      nlinarith [mul_nonneg (sub_nonneg.mpr hstatic16) hloglog]

def logPowerAbsorptionFactor (q : ℕ) : ℕ := (2 * q).factorial

lemma one_add_log_one_add_pow_two_mul_le
    {Y : ℝ} (hY : 0 ≤ Y) (q : ℕ) :
    (1 + Real.log (1 + Y)) ^ (2 * q) ≤
      3 * (logPowerAbsorptionFactor q : ℝ) * (1 + Y) := by
  let v := 1 + Real.log (1 + Y)
  have hOneY : 0 < 1 + Y := by linarith
  have hlog0 : 0 ≤ Real.log (1 + Y) :=
    Real.log_nonneg (by linarith)
  have hv0 : 0 ≤ v := by dsimp [v]; linarith
  have hseries := Real.pow_div_factorial_le_exp v hv0 (2 * q)
  have hfacPos : (0 : ℝ) < (logPowerAbsorptionFactor q : ℝ) := by
    rw [logPowerAbsorptionFactor]
    positivity
  have hpow : v ^ (2 * q) ≤
      (logPowerAbsorptionFactor q : ℝ) * Real.exp v := by
    have hseries' : v ^ (2 * q) / (logPowerAbsorptionFactor q : ℝ) ≤
        Real.exp v := by
      simpa only [logPowerAbsorptionFactor] using hseries
    apply (div_le_iff₀ hfacPos).mp at hseries'
    simpa only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hseries'
  have hexp : Real.exp v = Real.exp 1 * (1 + Y) := by
    dsimp [v]
    rw [Real.exp_add, Real.exp_log hOneY]
  rw [hexp] at hpow
  calc
    (1 + Real.log (1 + Y)) ^ (2 * q) = v ^ (2 * q) := rfl
    _ ≤ (logPowerAbsorptionFactor q : ℝ) * (Real.exp 1 * (1 + Y)) := hpow
    _ ≤ 3 * (logPowerAbsorptionFactor q : ℝ) * (1 + Y) := by
      have he : Real.exp 1 ≤ (3 : ℝ) := Real.exp_one_lt_three.le
      have hfac0 : 0 ≤ (logPowerAbsorptionFactor q : ℝ) := hfacPos.le
      have hOneY0 : 0 ≤ 1 + Y := hOneY.le
      nlinarith [mul_nonneg hfac0 hOneY0,
        mul_nonneg (sub_nonneg.mpr he) (mul_nonneg hfac0 hOneY0)]

lemma absorb_one_add_log_power
    {Y D L : ℝ} {q : ℕ}
    (hY : 0 ≤ Y) (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hineq : Y ≤ D * (1 + Real.log (1 + Y)) ^ q + L) :
    Y ≤ 1 + 2 * L + 24 * D ^ 2 * (logPowerAbsorptionFactor q : ℝ) := by
  let V := (1 + Real.log (1 + Y)) ^ q
  let F : ℝ := (logPowerAbsorptionFactor q : ℝ)
  have hV0 : 0 ≤ V := by
    dsimp [V]
    exact pow_nonneg (by
      have : 0 ≤ Real.log (1 + Y) := Real.log_nonneg (by linarith)
      linarith) _
  have hF0 : 0 ≤ F := by dsimp [F]; positivity
  have hV2 : V ^ 2 ≤ 3 * F * (1 + Y) := by
    have h := one_add_log_one_add_pow_two_mul_le hY q
    simpa only [V, F, ← pow_mul, mul_comm] using h
  by_contra hnot
  have hbig : 1 + 2 * L + 24 * D ^ 2 * F < Y := by
    simpa only [F] using lt_of_not_ge hnot
  have hYone : 1 < Y := by
    have hterm : 0 ≤ 24 * D ^ 2 * F := by positivity
    linarith
  have hLhalf : L < Y / 2 := by
    have hterm : 0 ≤ 24 * D ^ 2 * F := by positivity
    linarith
  have hhalf : Y / 2 ≤ D * V := by
    have hineq' : Y ≤ D * V + L := by simpa only [V] using hineq
    linarith
  have hsquare : (Y / 2) ^ 2 ≤ (D * V) ^ 2 := by
    exact pow_le_pow_left₀ (by positivity) hhalf 2
  have hDV : (D * V) ^ 2 ≤ D ^ 2 * (3 * F * (1 + Y)) := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hV2 (sq_nonneg D)
  have hOneY : 1 + Y ≤ 2 * Y := by linarith
  have hright : D ^ 2 * (3 * F * (1 + Y)) ≤
      6 * D ^ 2 * F * Y := by
    have hscale : 0 ≤ 3 * D ^ 2 * F := by positivity
    calc
      D ^ 2 * (3 * F * (1 + Y)) =
          (3 * D ^ 2 * F) * (1 + Y) := by ring
      _ ≤ (3 * D ^ 2 * F) * (2 * Y) :=
        mul_le_mul_of_nonneg_left hOneY hscale
      _ = 6 * D ^ 2 * F * Y := by ring
  have hYY : Y * Y ≤ (24 * D ^ 2 * F) * Y := by
    nlinarith [hsquare, hDV.trans hright]
  have hbound : Y ≤ 24 * D ^ 2 * F := by
    exact (mul_le_mul_iff_of_pos_right (by linarith : 0 < Y)).mp (by
      simpa only [mul_assoc] using hYY)
  linarith

noncomputable def pellAbsorptionD (H J : ℕ) : ℝ :=
  3 * pellThresholdStaticControl H J ^ 9900

noncomputable def pellAbsorptionL (H J : ℕ) : ℝ :=
  4 * pellExponentControl H * (J : ℝ)

noncomputable def pellHeightControl (H J : ℕ) : ℝ :=
  4 * (J : ℝ) +
    (1 + 2 * pellAbsorptionL H J +
      24 * pellAbsorptionD H J ^ 2 * (logPowerAbsorptionFactor 9900 : ℝ))

lemma pellExponentControl_pos (H : ℕ) : 0 < pellExponentControl H := by
  have hclass : 0 < pellClassControl H := by
    rw [pellClassControl]
    positivity
  have hindex : 0 < (pellIndexControl H : ℝ) := by
    rw [pellIndexControl, boundedUnitIndexCoarse]
    positivity
  rw [pellExponentControl]
  positivity

lemma pellThresholdControl_nonneg
    {H J x : ℕ} (hx : 0 < x) : 0 ≤ pellThresholdControl H J x := by
  have hcoef := pellCoefficientControl_nonneg (H := H) (J := J) hx
  have hunit := pellUnitBoxControl_nonneg (H := H) (J := J) hx
  have hlead := pellLeadingControl_nonneg H J
  have hcommon := pellCommonUnitControl_nonneg H
  have hlogH : 0 ≤ Real.log (H + 1 : ℕ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ H + 1 by omega))
  have hlogCoef : 0 ≤ Real.log (2 * pellCoefficientControl H J x + 5) :=
    Real.log_nonneg (by nlinarith)
  have hlogUnit : 0 ≤ Real.log (2 * pellUnitBoxControl H J x + 3) :=
    Real.log_nonneg (by nlinarith)
  rw [pellThresholdControl]
  positivity

lemma pellHeightControl_nonneg (H J : ℕ) : 0 ≤ pellHeightControl H J := by
  have hE := pellExponentControl_pos H
  have hT := pellThresholdStaticControl_pos H J
  have hJ : 0 ≤ (J : ℝ) := Nat.cast_nonneg _
  have hfac : 0 ≤ (logPowerAbsorptionFactor 9900 : ℝ) := Nat.cast_nonneg _
  have hD : 0 ≤ pellAbsorptionD H J := by
    rw [pellAbsorptionD]
    exact mul_nonneg (by norm_num) (pow_nonneg hT.le _)
  have hL : 0 ≤ pellAbsorptionL H J := by
    rw [pellAbsorptionL]
    exact mul_nonneg (mul_nonneg (by norm_num) hE.le) hJ
  have hmiddle : 0 ≤ 2 * pellAbsorptionL H J :=
    mul_nonneg (by norm_num) hL
  have hlast : 0 ≤ 24 * pellAbsorptionD H J ^ 2 *
      (logPowerAbsorptionFactor 9900 : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hfac
  rw [pellHeightControl]
  exact add_nonneg (mul_nonneg (by norm_num) hJ)
    (add_nonneg (add_nonneg (by norm_num) hmiddle) hlast)

/- DIAGNOSTICALLY DISABLED
theorem realPell_uniform_height_bound
    {γ₁ γ₂ γ₃ H x₁ x₂ x₃ J : ℕ} {β₁₂ β₁₃ : ℤ}
    (hPell : SimultaneousPellZ (γ₁ : ℤ) (γ₂ : ℤ) (γ₃ : ℤ)
      β₁₂ β₁₃ (x₁ : ℤ) (x₂ : ℤ) (x₃ : ℤ))
    (hβ₁₂ : β₁₂ ≠ 0) (hβ₁₃ : β₁₃ ≠ 0)
    (hβ₂₃ : β₁₃ - β₁₂ ≠ 0)
    (hJ₁₂ : β₁₂.natAbs ≤ J) (hJ₁₃ : β₁₃.natAbs ≤ J)
    (hJ₂₃ : (β₁₃ - β₁₂).natAbs ≤ J)
    (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂) (hγ₃ : 0 < γ₃)
    (hγ₁H : γ₁ ≤ H) (hγ₂H : γ₂ ≤ H) (hγ₃H : γ₃ ≤ H)
    (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) (hx₃ : 0 < x₃) :
    Real.log (x₁ : ℝ) ≤ pellHeightControl H J := by
  let Y := Real.log (x₁ : ℝ)
  have hY : 0 ≤ Y := by
    dsimp [Y]
    exact Real.log_nonneg (by exact_mod_cast hx₁)
  trace_state
  by_cases hlarge : 4 * J < γ₁ * x₁ ^ 2
  · have hcoord := realPell_uniform_log_coordinate_inequality hPell
      hβ₁₂ hβ₁₃ hβ₂₃ hJ₁₂ hJ₁₃ hJ₂₃ hγ₁ hγ₂ hγ₃
      hγ₁H hγ₂H hγ₃H hx₁ hx₂ hx₃ hlarge
    trace_state
    have hT := pellThresholdControl_le_static_mul_log
      (H := H) (J := J) hx₁
    have hT0 := pellThresholdControl_nonneg (H := H) (J := J) hx₁
    have hTpow := pow_le_pow_left₀ hT0 hT 9900
    have hpow : pellThresholdControl H J x₁ ^ 9900 ≤
        pellThresholdStaticControl H J ^ 9900 *
          (1 + Real.log (1 + Y)) ^ 9900 := by
      dsimp [Y] at hTpow ⊢
      simpa only [mul_pow] using hTpow
    trace_state
    have hJpos : (0 : ℝ) < J := by
      exact_mod_cast (Int.natAbs_pos.mpr hβ₁₂).trans_le hJ₁₂
    have hEpos := pellExponentControl_pos H
    have hApos : 0 < 4 * pellExponentControl H * (J : ℝ) :=
      mul_pos (mul_pos (by norm_num) hEpos) hJpos
    have hlogA := Real.log_le_sub_one_of_pos hApos
    have hD : 0 ≤ pellAbsorptionD H J := by
      rw [pellAbsorptionD]
      exact mul_nonneg (by norm_num) (pow_nonneg (pellThresholdStaticControl_pos H J).le _)
    have hL : 0 ≤ pellAbsorptionL H J := by
      rw [pellAbsorptionL]
      exact mul_nonneg (mul_nonneg (by norm_num) hEpos.le) hJpos.le
    have hineq : Y ≤ pellAbsorptionD H J *
        (1 + Real.log (1 + Y)) ^ 9900 + pellAbsorptionL H J := by
      dsimp [Y] at hcoord hpow hlogA ⊢
      rw [pellAbsorptionD, pellAbsorptionL]
      nlinarith
    trace_state
    have habsorb := absorb_one_add_log_power hY hD hL hineq
    trace_state
    trace_state
    change Y ≤ pellHeightControl H J
    rw [pellHeightControl]
    exact habsorb.trans
      (le_add_of_nonneg_left (mul_nonneg (by norm_num) (Nat.cast_nonneg J)))
  · have hsmall : γ₁ * x₁ ^ 2 ≤ 4 * J := by omega
    have hγone : 1 ≤ γ₁ := by omega
    have hxSq : x₁ ≤ x₁ ^ 2 := by nlinarith
    have hxJ : x₁ ≤ 4 * J := by
      calc
        x₁ ≤ x₁ ^ 2 := hxSq
        _ ≤ γ₁ * x₁ ^ 2 := by nlinarith
        _ ≤ 4 * J := hsmall
    have hlogx : Real.log (x₁ : ℝ) ≤ (x₁ : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (by exact_mod_cast hx₁)
    have hxJR : (x₁ : ℝ) ≤ 4 * (J : ℝ) := by exact_mod_cast hxJ
    have hE := pellExponentControl_pos H
    have hT := pellThresholdStaticControl_pos H J
    have hfac : 0 ≤ (logPowerAbsorptionFactor 9900 : ℝ) := Nat.cast_nonneg _
    have hD : 0 ≤ pellAbsorptionD H J := by
      rw [pellAbsorptionD]
      exact mul_nonneg (by norm_num) (pow_nonneg hT.le _)
    have hL : 0 ≤ pellAbsorptionL H J := by
      rw [pellAbsorptionL]
      exact mul_nonneg (mul_nonneg (by norm_num) hE.le) (Nat.cast_nonneg J)
    have htail : 0 ≤
        1 + 2 * pellAbsorptionL H J +
          24 * pellAbsorptionD H J ^ 2 * (logPowerAbsorptionFactor 9900 : ℝ) := by
      have hmiddle : 0 ≤ 2 * pellAbsorptionL H J :=
        mul_nonneg (by norm_num) hL
      have hlast : 0 ≤ 24 * pellAbsorptionD H J ^ 2 *
            (logPowerAbsorptionFactor 9900 : ℝ) :=
        mul_nonneg
          (mul_nonneg (by norm_num) (sq_nonneg (pellAbsorptionD H J))) hfac
      linarith
    rw [pellHeightControl]
    linarith
-/

theorem realPell_uniform_absorption_inequality_of_large
    {γ₁ γ₂ γ₃ H x₁ x₂ x₃ J : ℕ} {β₁₂ β₁₃ : ℤ}
    (hPell : SimultaneousPellZ (γ₁ : ℤ) (γ₂ : ℤ) (γ₃ : ℤ)
      β₁₂ β₁₃ (x₁ : ℤ) (x₂ : ℤ) (x₃ : ℤ))
    (hβ₁₂ : β₁₂ ≠ 0) (hβ₁₃ : β₁₃ ≠ 0)
    (hβ₂₃ : β₁₃ - β₁₂ ≠ 0)
    (hJ₁₂ : β₁₂.natAbs ≤ J) (hJ₁₃ : β₁₃.natAbs ≤ J)
    (hJ₂₃ : (β₁₃ - β₁₂).natAbs ≤ J)
    (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂) (hγ₃ : 0 < γ₃)
    (hγ₁H : γ₁ ≤ H) (hγ₂H : γ₂ ≤ H) (hγ₃H : γ₃ ≤ H)
    (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) (hx₃ : 0 < x₃)
    (hlarge : 4 * J < γ₁ * x₁ ^ 2) :
    Real.log (x₁ : ℝ) ≤ pellAbsorptionD H J *
      (1 + Real.log (1 + Real.log (x₁ : ℝ))) ^ 9900 +
        pellAbsorptionL H J := by
  let Y := Real.log (x₁ : ℝ)
  have hY : 0 ≤ Y := by
    dsimp [Y]
    exact Real.log_nonneg (by exact_mod_cast hx₁)
  have hcoord := realPell_uniform_log_coordinate_inequality hPell
    hβ₁₂ hβ₁₃ hβ₂₃ hJ₁₂ hJ₁₃ hJ₂₃ hγ₁ hγ₂ hγ₃
    hγ₁H hγ₂H hγ₃H hx₁ hx₂ hx₃ hlarge
  have hT := pellThresholdControl_le_static_mul_log
    (H := H) (J := J) hx₁
  have hT0 := pellThresholdControl_nonneg (H := H) (J := J) hx₁
  have hTpow := pow_le_pow_left₀ hT0 hT 9900
  have hpow : pellThresholdControl H J x₁ ^ 9900 ≤
      pellThresholdStaticControl H J ^ 9900 *
        (1 + Real.log (1 + Y)) ^ 9900 := by
    dsimp [Y] at hTpow ⊢
    simpa only [mul_pow] using hTpow
  have hJpos : (0 : ℝ) < J := by
    exact_mod_cast (Int.natAbs_pos.mpr hβ₁₂).trans_le hJ₁₂
  have hEpos := pellExponentControl_pos H
  have hApos : 0 < 4 * pellExponentControl H * (J : ℝ) :=
    mul_pos (mul_pos (by norm_num) hEpos) hJpos
  have hlogA := Real.log_le_sub_one_of_pos hApos
  have hineq : Y ≤ pellAbsorptionD H J *
      (1 + Real.log (1 + Y)) ^ 9900 + pellAbsorptionL H J := by
    let V := (1 + Real.log (1 + Y)) ^ 9900
    let A := 4 * pellExponentControl H * (J : ℝ)
    have hfirst : Y ≤ 2 * Y := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 2 by norm_num) hY
    calc
      Y ≤ 2 * Y := hfirst
      _ ≤ 3 * pellThresholdControl H J x₁ ^ 9900 + Real.log A := by
        simpa only [Y, A] using hcoord
      _ ≤ 3 * (pellThresholdStaticControl H J ^ 9900 * V) + (A - 1) :=
        add_le_add (mul_le_mul_of_nonneg_left (by simpa only [V] using hpow)
          (by norm_num)) (by simpa only [A] using hlogA)
      _ ≤ 3 * (pellThresholdStaticControl H J ^ 9900 * V) + A := by
        exact add_le_add (le_refl _)
          (sub_le_self A (by norm_num : (0 : ℝ) ≤ 1))
      _ = pellAbsorptionD H J * V + pellAbsorptionL H J := by
        rw [pellAbsorptionD, pellAbsorptionL]
        rw [mul_assoc]
      _ = pellAbsorptionD H J *
          (1 + Real.log (1 + Y)) ^ 9900 + pellAbsorptionL H J := rfl
  simpa only [Y] using hineq

theorem realPell_uniform_height_bound_of_large
    {γ₁ γ₂ γ₃ H x₁ x₂ x₃ J : ℕ} {β₁₂ β₁₃ : ℤ}
    (hPell : SimultaneousPellZ (γ₁ : ℤ) (γ₂ : ℤ) (γ₃ : ℤ)
      β₁₂ β₁₃ (x₁ : ℤ) (x₂ : ℤ) (x₃ : ℤ))
    (hβ₁₂ : β₁₂ ≠ 0) (hβ₁₃ : β₁₃ ≠ 0)
    (hβ₂₃ : β₁₃ - β₁₂ ≠ 0)
    (hJ₁₂ : β₁₂.natAbs ≤ J) (hJ₁₃ : β₁₃.natAbs ≤ J)
    (hJ₂₃ : (β₁₃ - β₁₂).natAbs ≤ J)
    (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂) (hγ₃ : 0 < γ₃)
    (hγ₁H : γ₁ ≤ H) (hγ₂H : γ₂ ≤ H) (hγ₃H : γ₃ ≤ H)
    (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) (hx₃ : 0 < x₃)
    (hlarge : 4 * J < γ₁ * x₁ ^ 2) :
    Real.log (x₁ : ℝ) ≤ pellHeightControl H J := by
  let Y := Real.log (x₁ : ℝ)
  have hY : 0 ≤ Y := by
    dsimp [Y]
    exact Real.log_nonneg (by exact_mod_cast hx₁)
  have hineq : Y ≤ pellAbsorptionD H J *
      (1 + Real.log (1 + Y)) ^ 9900 + pellAbsorptionL H J := by
    simpa only [Y] using realPell_uniform_absorption_inequality_of_large
      hPell hβ₁₂ hβ₁₃ hβ₂₃ hJ₁₂ hJ₁₃ hJ₂₃ hγ₁ hγ₂ hγ₃
      hγ₁H hγ₂H hγ₃H hx₁ hx₂ hx₃ hlarge
  have hD : 0 ≤ pellAbsorptionD H J := by
    rw [pellAbsorptionD]
    exact mul_nonneg (by norm_num)
      (pow_nonneg (pellThresholdStaticControl_pos H J).le _)
  have hL : 0 ≤ pellAbsorptionL H J := by
    rw [pellAbsorptionL]
    exact mul_nonneg (mul_nonneg (by norm_num) (pellExponentControl_pos H).le)
      (Nat.cast_nonneg J)
  have habsorb := absorb_one_add_log_power hY hD hL hineq
  change Y ≤ pellHeightControl H J
  rw [pellHeightControl]
  exact habsorb.trans
    (le_add_of_nonneg_left (mul_nonneg (by norm_num) (Nat.cast_nonneg J)))

lemma four_mul_le_pellHeightControl (H J : ℕ) :
    4 * (J : ℝ) ≤ pellHeightControl H J := by
  have hfac : 0 ≤ (logPowerAbsorptionFactor 9900 : ℝ) := Nat.cast_nonneg _
  have hD : 0 ≤ pellAbsorptionD H J := by
    rw [pellAbsorptionD]
    exact mul_nonneg (by norm_num)
      (pow_nonneg (pellThresholdStaticControl_pos H J).le _)
  have hL : 0 ≤ pellAbsorptionL H J := by
    rw [pellAbsorptionL]
    exact mul_nonneg (mul_nonneg (by norm_num) (pellExponentControl_pos H).le)
      (Nat.cast_nonneg J)
  have htail : 0 ≤ 1 + 2 * pellAbsorptionL H J +
      24 * pellAbsorptionD H J ^ 2 *
        (logPowerAbsorptionFactor 9900 : ℝ) := by
    exact add_nonneg
      (add_nonneg (by norm_num) (mul_nonneg (by norm_num) hL))
      (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hfac)
  rw [pellHeightControl]
  exact le_add_of_nonneg_right htail

theorem realPell_uniform_height_bound
    {γ₁ γ₂ γ₃ H x₁ x₂ x₃ J : ℕ} {β₁₂ β₁₃ : ℤ}
    (hPell : SimultaneousPellZ (γ₁ : ℤ) (γ₂ : ℤ) (γ₃ : ℤ)
      β₁₂ β₁₃ (x₁ : ℤ) (x₂ : ℤ) (x₃ : ℤ))
    (hβ₁₂ : β₁₂ ≠ 0) (hβ₁₃ : β₁₃ ≠ 0)
    (hβ₂₃ : β₁₃ - β₁₂ ≠ 0)
    (hJ₁₂ : β₁₂.natAbs ≤ J) (hJ₁₃ : β₁₃.natAbs ≤ J)
    (hJ₂₃ : (β₁₃ - β₁₂).natAbs ≤ J)
    (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂) (hγ₃ : 0 < γ₃)
    (hγ₁H : γ₁ ≤ H) (hγ₂H : γ₂ ≤ H) (hγ₃H : γ₃ ≤ H)
    (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) (hx₃ : 0 < x₃) :
    Real.log (x₁ : ℝ) ≤ pellHeightControl H J := by
  by_cases hlarge : 4 * J < γ₁ * x₁ ^ 2
  · exact realPell_uniform_height_bound_of_large hPell hβ₁₂ hβ₁₃ hβ₂₃
      hJ₁₂ hJ₁₃ hJ₂₃ hγ₁ hγ₂ hγ₃ hγ₁H hγ₂H hγ₃H
      hx₁ hx₂ hx₃ hlarge
  · have hsmall : γ₁ * x₁ ^ 2 ≤ 4 * J := by omega
    have hγone : 1 ≤ γ₁ := by omega
    have hxSq : x₁ ≤ x₁ ^ 2 := by nlinarith
    have hxJ : x₁ ≤ 4 * J := by
      calc
        x₁ ≤ x₁ ^ 2 := hxSq
        _ ≤ γ₁ * x₁ ^ 2 := by nlinarith
        _ ≤ 4 * J := hsmall
    have hlogx : Real.log (x₁ : ℝ) ≤ (x₁ : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (by exact_mod_cast hx₁)
    have hxJR : (x₁ : ℝ) ≤ 4 * (J : ℝ) := by exact_mod_cast hxJ
    exact (hlogx.trans (by linarith)).trans (four_mul_le_pellHeightControl H J)

def TwoPolynomiallyBounded (f : ℕ → ℕ → ℝ) : Prop :=
  ∃ d : ℕ, ∀ H J, 0 ≤ f H J ∧ f H J ≤ ((H + J + 2 : ℕ) : ℝ) ^ d

lemma twoPolynomiallyBounded_const {c : ℝ} (hc : 0 ≤ c) :
    TwoPolynomiallyBounded (fun _ _ ↦ c) := by
  refine ⟨Nat.ceil c, fun H J ↦ ⟨hc, ?_⟩⟩
  have hcceil : c ≤ (Nat.ceil c : ℝ) := Nat.le_ceil c
  have hnat : Nat.ceil c ≤ 2 ^ Nat.ceil c := by
    induction Nat.ceil c with
    | zero => simp
    | succ d hd =>
        have hone : 1 ≤ 2 ^ d := Nat.one_le_two_pow
        rw [pow_succ]
        omega
  have hcast : (Nat.ceil c : ℝ) ≤ (2 : ℝ) ^ Nat.ceil c := by
    exact_mod_cast hnat
  have hbase : (2 : ℝ) ≤ ((H + J + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 2 ≤ H + J + 2 by omega)
  exact hcceil.trans (hcast.trans (pow_le_pow_left₀ (by norm_num) hbase _))

lemma twoPolynomiallyBounded_H :
    TwoPolynomiallyBounded (fun H _ ↦ (H : ℝ)) := by
  refine ⟨1, fun H J ↦ ⟨by positivity, ?_⟩⟩
  norm_num
  exact_mod_cast (show H ≤ H + J + 2 by omega)

lemma twoPolynomiallyBounded_J :
    TwoPolynomiallyBounded (fun _ J ↦ (J : ℝ)) := by
  refine ⟨1, fun H J ↦ ⟨by positivity, ?_⟩⟩
  norm_num
  exact_mod_cast (show J ≤ H + J + 2 by omega)

lemma TwoPolynomiallyBounded.add {f g : ℕ → ℕ → ℝ}
    (hf : TwoPolynomiallyBounded f) (hg : TwoPolynomiallyBounded g) :
    TwoPolynomiallyBounded (fun H J ↦ f H J + g H J) := by
  rcases hf with ⟨a, ha⟩
  rcases hg with ⟨b, hb⟩
  refine ⟨a + b + 1, fun H J ↦ ⟨add_nonneg (ha H J).1 (hb H J).1, ?_⟩⟩
  let S : ℝ := ((H + J + 2 : ℕ) : ℝ)
  have hS2 : (2 : ℝ) ≤ S := by
    dsimp [S]
    exact_mod_cast (show 2 ≤ H + J + 2 by omega)
  have hS1 : (1 : ℝ) ≤ S := by linarith
  have ha' : f H J ≤ S ^ (a + b) :=
    (ha H J).2.trans (pow_le_pow_right₀ hS1 (by omega))
  have hb' : g H J ≤ S ^ (a + b) :=
    (hb H J).2.trans (pow_le_pow_right₀ hS1 (by omega))
  calc
    f H J + g H J ≤ 2 * S ^ (a + b) := by linarith
    _ ≤ S * S ^ (a + b) :=
      mul_le_mul_of_nonneg_right hS2 (pow_nonneg (by positivity) _)
    _ = S ^ (a + b + 1) := by rw [pow_succ]; ring

lemma TwoPolynomiallyBounded.mul {f g : ℕ → ℕ → ℝ}
    (hf : TwoPolynomiallyBounded f) (hg : TwoPolynomiallyBounded g) :
    TwoPolynomiallyBounded (fun H J ↦ f H J * g H J) := by
  rcases hf with ⟨a, ha⟩
  rcases hg with ⟨b, hb⟩
  refine ⟨a + b, fun H J ↦ ⟨mul_nonneg (ha H J).1 (hb H J).1, ?_⟩⟩
  calc
    f H J * g H J ≤
        (((H + J + 2 : ℕ) : ℝ) ^ a) * (((H + J + 2 : ℕ) : ℝ) ^ b) :=
      mul_le_mul (ha H J).2 (hb H J).2 (hb H J).1 (by positivity)
    _ = ((H + J + 2 : ℕ) : ℝ) ^ (a + b) := by rw [pow_add]

lemma TwoPolynomiallyBounded.pow {f : ℕ → ℕ → ℝ}
    (hf : TwoPolynomiallyBounded f) (k : ℕ) :
    TwoPolynomiallyBounded (fun H J ↦ (f H J) ^ k) := by
  rcases hf with ⟨a, ha⟩
  refine ⟨a * k, fun H J ↦ ⟨pow_nonneg (ha H J).1 _, ?_⟩⟩
  calc
    (f H J) ^ k ≤ (((H + J + 2 : ℕ) : ℝ) ^ a) ^ k :=
      pow_le_pow_left₀ (ha H J).1 (ha H J).2 _
    _ = ((H + J + 2 : ℕ) : ℝ) ^ (a * k) := by rw [pow_mul]

lemma TwoPolynomiallyBounded.log {f : ℕ → ℕ → ℝ}
    (hf : TwoPolynomiallyBounded f) (hone : ∀ H J, 1 ≤ f H J) :
    TwoPolynomiallyBounded (fun H J ↦ Real.log (f H J)) := by
  rcases hf with ⟨a, ha⟩
  refine ⟨a, fun H J ↦ ⟨Real.log_nonneg (hone H J), ?_⟩⟩
  exact (Real.log_le_sub_one_of_pos (lt_of_lt_of_le zero_lt_one (hone H J))).trans
    ((sub_le_self _ (by norm_num)).trans (ha H J).2)

lemma TwoPolynomiallyBounded.mono {f g : ℕ → ℕ → ℝ}
    (hf : TwoPolynomiallyBounded f) (hg0 : ∀ H J, 0 ≤ g H J)
    (hgf : ∀ H J, g H J ≤ f H J) : TwoPolynomiallyBounded g := by
  rcases hf with ⟨a, ha⟩
  exact ⟨a, fun H J ↦ ⟨hg0 H J, (hgf H J).trans (ha H J).2⟩⟩

theorem pellHeightControl_twoPolynomiallyBounded :
    TwoPolynomiallyBounded pellHeightControl := by
  have hC (c : ℝ) (hc : 0 ≤ c) :
      TwoPolynomiallyBounded (fun _ _ ↦ c) :=
    twoPolynomiallyBounded_const hc
  have hH := twoPolynomiallyBounded_H
  have hJ := twoPolynomiallyBounded_J
  have hOne := hC 1 (by norm_num)
  have hTwo := hC 2 (by norm_num)
  have hH1 : TwoPolynomiallyBounded (fun H _ ↦ (H + 1 : ℕ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hH.add hOne
  have hJ1 : TwoPolynomiallyBounded (fun _ J ↦ (J + 1 : ℕ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hJ.add hOne
  have hHJ1 : TwoPolynomiallyBounded (fun H J ↦ (H + J + 1 : ℕ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (hH.add hJ).add hOne
  have hlogH1 : TwoPolynomiallyBounded
      (fun H _ ↦ Real.log (H + 1 : ℕ)) :=
    hH1.log (fun H J ↦ by exact_mod_cast (show 1 ≤ H + 1 by omega))
  have hlogJ1 : TwoPolynomiallyBounded
      (fun _ J ↦ Real.log (J + 1 : ℕ)) :=
    hJ1.log (fun H J ↦ by exact_mod_cast (show 1 ≤ J + 1 by omega))
  have hlogHJ1 : TwoPolynomiallyBounded
      (fun H J ↦ Real.log (H + J + 1 : ℕ)) :=
    hHJ1.log (fun H J ↦ by exact_mod_cast (show 1 ≤ H + J + 1 by omega))
  have hMink : TwoPolynomiallyBounded
      (fun H _ ↦ (pellMinkowskiControl H : ℝ)) := by
    simpa only [pellMinkowskiControl, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat, Nat.cast_pow] using
      (hC 258 (by norm_num)).mul
        (((hC 40320 (by norm_num)).mul (hH1.pow 24)).pow 2 |>.add hOne)
  have hClass : TwoPolynomiallyBounded (fun H _ ↦ pellClassControl H) := by
    simpa only [pellClassControl, Nat.cast_add, Nat.cast_one, Nat.cast_pow,
      Nat.cast_ofNat] using
      (hC ((6 : ℝ) ^ 8) (by positivity)).mul
        (((hC 40320 (by norm_num)).mul (hH1.pow 24)).pow 2)
  have hCommon : TwoPolynomiallyBounded (fun H _ ↦ pellCommonUnitControl H) := by
    simpa only [pellCommonUnitControl, Nat.cast_add, Nat.cast_one, Nat.cast_pow,
      Nat.cast_ofNat] using
      (hC 100000000 (by norm_num)).mul ((hMink.add hOne).pow 3)
  have hIndex : TwoPolynomiallyBounded
      (fun H _ ↦ (pellIndexControl H : ℝ)) := by
    simpa only [pellIndexControl, boundedUnitIndexCoarse, Nat.cast_mul,
      Nat.cast_pow, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using
      (((hC 40320 (by norm_num)).mul ((hC 264 (by norm_num)).pow 8)).mul
        ((hC 100000000 (by norm_num)).pow 8)).mul ((hMink.add hOne).pow 24)
  have hSupport : TwoPolynomiallyBounded (fun _ J ↦ pellSupportControl J) := by
    simpa only [pellSupportControl, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using
      (hC 24 (by norm_num)).mul hJ1
  have hPrimeGenerator : TwoPolynomiallyBounded pellPrimeGeneratorControl := by
    change TwoPolynomiallyBounded (fun H J ↦
      128 * pellCommonUnitControl H +
        136 * pellClassControl H * Real.log (J + 1 : ℕ))
    exact ((hC 128 (by norm_num)).mul hCommon).add
      (((hC 136 (by norm_num)).mul hClass).mul hlogJ1)
  have hPrimeProduct : TwoPolynomiallyBounded pellPrimeProductControl := by
    change TwoPolynomiallyBounded (fun H J ↦
      pellSupportControl J * (((J + 1 : ℕ) : ℝ) ^ 16) *
        pellPrimeGeneratorControl H J)
    exact (hSupport.mul (hJ1.pow 16)).mul hPrimeGenerator
  have hRatio : TwoPolynomiallyBounded (fun _ J ↦ pellRatioControl J) := by
    simpa only [pellRatioControl] using (hC 16 (by norm_num)).mul hlogJ1
  have hLeading : TwoPolynomiallyBounded pellLeadingControl := by
    change TwoPolynomiallyBounded (fun H J ↦
      (2 * (pellClassControl H * (pellIndexControl H : ℝ))) *
          pellRatioControl J +
        (((2 * pellIndexControl H : ℕ) : ℝ)) * pellPrimeProductControl H J)
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      ((((hC 2 (by norm_num)).mul (hClass.mul hIndex)).mul hRatio).add
        (((hC 2 (by norm_num)).mul hIndex).mul hPrimeProduct))
  have hResidualAffine : TwoPolynomiallyBounded pellResidualAffineControl := by
    change TwoPolynomiallyBounded (fun H J ↦
      pellClassControl H * 100 * (1 + Real.log (H + J + 1 : ℕ)) +
        pellPrimeProductControl H J + 100 * pellClassControl H)
    exact (((hClass.mul (hC 100 (by norm_num))).mul (hOne.add hlogHJ1)).add
      hPrimeProduct).add ((hC 100 (by norm_num)).mul hClass)
  have hCoordinateStatic : TwoPolynomiallyBounded pellCoordinateStaticControl := by
    change TwoPolynomiallyBounded (fun H J ↦
      1 + pellCommonUnitControl H +
        (pellIndexControl H : ℝ) * (2 * pellResidualAffineControl H J))
    exact (hOne.add hCommon).add
      (hIndex.mul ((hC 2 (by norm_num)).mul hResidualAffine))
  have hCoefficientStatic : TwoPolynomiallyBounded pellCoefficientStaticControl := by
    change TwoPolynomiallyBounded (fun H J ↦
      40320 * (264 : ℝ) ^ 8 * pellCoordinateStaticControl H J ^ 8)
    exact ((hC 40320 (by norm_num)).mul ((hC 264 (by norm_num)).pow 8)).mul
      (hCoordinateStatic.pow 8)
  have hAbsCoordinate : TwoPolynomiallyBounded
      pellAbsorptionCoordinateBaseControl := by
    change TwoPolynomiallyBounded (fun H J ↦
      1 + pellCommonUnitControl H +
        (pellIndexControl H : ℝ) * (2 * pellLeadingControl H J))
    exact (hOne.add hCommon).add
      (hIndex.mul ((hC 2 (by norm_num)).mul hLeading))
  have hAbsCoefficient : TwoPolynomiallyBounded
      pellAbsorptionCoefficientControl := by
    change TwoPolynomiallyBounded (fun H J ↦
      40320 * (264 : ℝ) ^ 8 * pellAbsorptionCoordinateBaseControl H J ^ 8)
    exact ((hC 40320 (by norm_num)).mul ((hC 264 (by norm_num)).pow 8)).mul
      (hAbsCoordinate.pow 8)
  have hUnitStatic : TwoPolynomiallyBounded pellUnitBoxStaticControl := by
    change TwoPolynomiallyBounded (fun H J ↦
      pellAbsorptionCoefficientControl H J + 1 +
        2 * (pellIndexControl H : ℝ) * (pellCoefficientStaticControl H J + 2))
    exact (hAbsCoefficient.add hOne).add
      (((hC 2 (by norm_num)).mul hIndex).mul
        (hCoefficientStatic.add (hC 2 (by norm_num))))
  have hCoefArg : TwoPolynomiallyBounded
      (fun H J ↦ 2 * pellCoefficientStaticControl H J + 5) :=
    ((hC 2 (by norm_num)).mul hCoefficientStatic).add (hC 5 (by norm_num))
  have hUnitArg : TwoPolynomiallyBounded
      (fun H J ↦ 2 * pellUnitBoxStaticControl H J + 3) :=
    ((hC 2 (by norm_num)).mul hUnitStatic).add (hC 3 (by norm_num))
  have hLogCoef := hCoefArg.log (fun H J ↦ by
    nlinarith [pellCoefficientStaticControl_pos H J])
  have hLogUnit := hUnitArg.log (fun H J ↦ by
    nlinarith [pellUnitBoxStaticControl_pos H J])
  have hThresholdStatic : TwoPolynomiallyBounded pellThresholdStaticControl := by
    change TwoPolynomiallyBounded (fun H J ↦
      (1000000000000000000000000000000 : ℝ) +
        3 * Real.log (H + 1 : ℕ) +
        Real.log (2 * pellCoefficientStaticControl H J + 5) +
        Real.log (2 * pellUnitBoxStaticControl H J + 3) +
        2 * (pellLeadingControl H J + 128 * pellCommonUnitControl H) + 16)
    exact (((((hC 1000000000000000000000000000000 (by norm_num)).add
        ((hC 3 (by norm_num)).mul hlogH1)).add hLogCoef).add hLogUnit).add
          ((hC 2 (by norm_num)).mul
            (hLeading.add ((hC 128 (by norm_num)).mul hCommon)))).add
        (hC 16 (by norm_num))
  have hExponent : TwoPolynomiallyBounded (fun H _ ↦ pellExponentControl H) := by
    simpa only [pellExponentControl] using
      (((hC 2 (by norm_num)).mul hClass).mul hIndex).add
        (((hC 4 (by norm_num)).mul hClass).mul (hIndex.pow 2))
  have hD : TwoPolynomiallyBounded pellAbsorptionD := by
    change TwoPolynomiallyBounded (fun H J ↦
      3 * pellThresholdStaticControl H J ^ 9900)
    exact (hC 3 (by norm_num)).mul (hThresholdStatic.pow 9900)
  have hL : TwoPolynomiallyBounded pellAbsorptionL := by
    change TwoPolynomiallyBounded (fun H J ↦
      4 * pellExponentControl H * (J : ℝ))
    exact ((hC 4 (by norm_num)).mul hExponent).mul hJ
  have hFactor : TwoPolynomiallyBounded
      (fun _ _ ↦ (logPowerAbsorptionFactor 9900 : ℝ)) :=
    hC _ (Nat.cast_nonneg _)
  change TwoPolynomiallyBounded (fun H J ↦
    4 * (J : ℝ) +
      (1 + 2 * pellAbsorptionL H J +
        24 * pellAbsorptionD H J ^ 2 * (logPowerAbsorptionFactor 9900 : ℝ)))
  exact ((hC 4 (by norm_num)).mul hJ).add
    (((hOne.add ((hC 2 (by norm_num)).mul hL)).add
      (((hC 24 (by norm_num)).mul (hD.pow 2)).mul hFactor)))

noncomputable def pellHeightDegree : ℕ :=
  Classical.choose pellHeightControl_twoPolynomiallyBounded

lemma pellHeightControl_le_degree_pow (H J : ℕ) :
    pellHeightControl H J ≤ ((H + J + 2 : ℕ) : ℝ) ^ pellHeightDegree := by
  exact (Classical.choose_spec pellHeightControl_twoPolynomiallyBounded H J).2

theorem simultaneousPell_loglog_le_degree_log
    {n i γ₁ γ₂ γ₃ H x₁ x₂ x₃ J : ℕ} {β₁₂ β₁₃ : ℤ}
    (hdecomp : x₁ ^ 2 * γ₁ = n + i)
    (hPell : SimultaneousPellZ (γ₁ : ℤ) (γ₂ : ℤ) (γ₃ : ℤ)
      β₁₂ β₁₃ (x₁ : ℤ) (x₂ : ℤ) (x₃ : ℤ))
    (hβ₁₂ : β₁₂ ≠ 0) (hβ₁₃ : β₁₃ ≠ 0)
    (hβ₂₃ : β₁₃ - β₁₂ ≠ 0)
    (hJ₁₂ : β₁₂.natAbs ≤ J) (hJ₁₃ : β₁₃.natAbs ≤ J)
    (hJ₂₃ : (β₁₃ - β₁₂).natAbs ≤ J)
    (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂) (hγ₃ : 0 < γ₃)
    (hγ₁H : γ₁ ≤ H) (hγ₂H : γ₂ ≤ H) (hγ₃H : γ₃ ≤ H)
    (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) (hx₃ : 0 < x₃)
    (hnlarge : 1 < n) :
    Real.log (Real.log (n : ℝ)) ≤
      ((pellHeightDegree + 4 : ℕ) : ℝ) * Real.log (H + J + 2 : ℕ) := by
  let S : ℝ := ((H + J + 2 : ℕ) : ℝ)
  let d := pellHeightDegree
  have hS2 : (2 : ℝ) ≤ S := by
    dsimp [S]
    exact_mod_cast (show 2 ≤ H + J + 2 by omega)
  have hS1 : (1 : ℝ) ≤ S := by linarith
  have hheight0 := realPell_uniform_height_bound hPell hβ₁₂ hβ₁₃ hβ₂₃
    hJ₁₂ hJ₁₃ hJ₂₃ hγ₁ hγ₂ hγ₃ hγ₁H hγ₂H hγ₃H
    hx₁ hx₂ hx₃
  have hheight : Real.log (x₁ : ℝ) ≤ S ^ d :=
    hheight0.trans (by simpa [S, d] using pellHeightControl_le_degree_pow H J)
  have hnpos : (0 : ℝ) < n := by positivity
  have hγR : (0 : ℝ) < γ₁ := by exact_mod_cast hγ₁
  have hxR : (0 : ℝ) < x₁ := by exact_mod_cast hx₁
  have hnprod : (n : ℝ) ≤ (γ₁ : ℝ) * (x₁ : ℝ) ^ 2 := by
    have hnat : n ≤ γ₁ * x₁ ^ 2 := by
      rw [Nat.mul_comm]
      omega
    exact_mod_cast hnat
  have hlogn : Real.log (n : ℝ) ≤
      Real.log (γ₁ : ℝ) + 2 * Real.log (x₁ : ℝ) := by
    calc
      Real.log (n : ℝ) ≤ Real.log ((γ₁ : ℝ) * (x₁ : ℝ) ^ 2) :=
        Real.log_le_log hnpos hnprod
      _ = Real.log (γ₁ : ℝ) + Real.log ((x₁ : ℝ) ^ 2) := by
        rw [Real.log_mul hγR.ne' (pow_ne_zero _ hxR.ne')]
      _ = Real.log (γ₁ : ℝ) + 2 * Real.log (x₁ : ℝ) := by
        rw [Real.log_pow]
        norm_num
  have hlogγ : Real.log (γ₁ : ℝ) ≤ S := by
    calc
      Real.log (γ₁ : ℝ) ≤ (γ₁ : ℝ) := Real.log_le_self hγR.le
      _ ≤ (H : ℝ) := by exact_mod_cast hγ₁H
      _ ≤ S := by
        dsimp [S]
        exact_mod_cast (show H ≤ H + J + 2 by omega)
  have hSd : S ^ d ≤ S ^ (d + 2) :=
    pow_le_pow_right₀ hS1 (by omega)
  have hS : S ≤ S ^ (d + 2) := by
    simpa only [pow_one] using pow_le_pow_right₀ hS1 (by omega : 1 ≤ d + 2)
  have hlognPow : Real.log (n : ℝ) ≤ S ^ (d + 4) := by
    calc
      Real.log (n : ℝ) ≤ Real.log (γ₁ : ℝ) + 2 * Real.log (x₁ : ℝ) := hlogn
      _ ≤ S ^ (d + 2) + 2 * S ^ (d + 2) := by
        exact add_le_add (hlogγ.trans hS)
          (mul_le_mul_of_nonneg_left (hheight.trans hSd)
            (by norm_num : (0 : ℝ) ≤ 2))
      _ = 3 * S ^ (d + 2) := by ring
      _ ≤ S ^ 2 * S ^ (d + 2) := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by positivity) _)
        nlinarith
      _ = S ^ (d + 4) := by rw [← pow_add]; congr 1; omega
  have hlognPos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast hnlarge)
  have hlogPow : Real.log (S ^ (d + 4)) =
      ((d + 4 : ℕ) : ℝ) * Real.log S := by rw [Real.log_pow]
  calc
    Real.log (Real.log (n : ℝ)) ≤ Real.log (S ^ (d + 4)) :=
      Real.log_le_log hlognPos hlognPow
    _ = ((d + 4 : ℕ) : ℝ) * Real.log S := hlogPow
    _ = ((pellHeightDegree + 4 : ℕ) : ℝ) *
        Real.log (H + J + 2 : ℕ) := rfl

theorem direct_pell_loglog_bound
    {n J : ℕ} {I : Finset ℕ}
    (hn : 0 < n) (hnlarge : 1 < n) (hfar : 4 * J < n)
    (hI : I ⊆ Finset.Icc 0 J) (hcard : 3 ≤ I.card)
    (hsquare : IsSquare (∏ j ∈ I, (n + j))) :
    Real.log (Real.log (n : ℝ)) ≤
      ((pellHeightDegree + 4 : ℕ) : ℝ) *
        Real.log (J ^ (I.card - 1) + 2 * J + 2 : ℕ) := by
  obtain ⟨i, hi, j, hj, k, hk, hij, hik, hjk, hdata⟩ :=
    exists_three_direct_pell_data hn hfar hI hcard hsquare
  dsimp only at hdata
  rcases hdata with ⟨hPell, hγi, hγj, hγk, hγiH, hγjH, hγkH,
    hxi, hxj, hxk, hβ₁₂, hβ₁₃, hβ₂₃, hJ₁₂, hJ₁₃, hJ₂₃, _hfar⟩
  exact simultaneousPell_loglog_le_degree_log
    (squareRootPart_sq_mul_squarefreePart (n + i)) hPell
    hβ₁₂ hβ₁₃ hβ₂₃ hJ₁₂ hJ₁₃ hJ₂₃
    hγi hγj hγk hγiH hγjH hγkH hxi hxj hxk hnlarge

lemma max_three_pow_le_pell {a b c R X : ℕ}
    (ha : a ^ R ≤ X) (hb : b ^ R ≤ X) (hc : c ^ R ≤ X) :
    max a (max b c) ^ R ≤ X := by
  by_cases haMax : a ≤ max b c
  · rw [max_eq_right haMax]
    by_cases hbc : b ≤ c
    · rwa [max_eq_right hbc]
    · rw [max_eq_left (Nat.le_of_not_ge hbc)]
      exact hb
  · rw [max_eq_left (Nat.le_of_not_ge haMax)]
    exact ha

theorem sparse_pell_loglog_bound_data
    {n J : ℕ} {I K : Finset ℕ}
    (hnlarge : 1 < n) (hI : I ⊆ Finset.Icc 0 J) (hK : K ⊆ I)
    (hcard : 3 ≤ K.card) (hJ : 1 ≤ J)
    (hsquare : IsSquare (∏ a ∈ I, (n + a))) :
    ∃ H : ℕ,
      0 < H ∧
      H ^ (K.card - 2) ≤
        J ^ (Nat.primeCounting J + K.card ^ 2 * Nat.log 2 J) ∧
      Real.log (Real.log (n : ℝ)) ≤
        ((pellHeightDegree + 4 : ℕ) : ℝ) *
          Real.log (H + 2 * J + 2 : ℕ) := by
  obtain ⟨i, hi, j, hj, k, hk, hij, hik, hjk, hiPow, hjPow, hkPow⟩ :=
    exists_three_sparse_shifts_with_power_bounds_subfamily
      (by omega : 0 < n) hI hK hcard hJ hsquare
  let γ₁ := squarefreePart (n + i)
  let γ₂ := squarefreePart (n + j)
  let γ₃ := squarefreePart (n + k)
  let x₁ := squareRootPart (n + i)
  let x₂ := squareRootPart (n + j)
  let x₃ := squareRootPart (n + k)
  let β₁₂ : ℤ := (i : ℤ) - j
  let β₁₃ : ℤ := (i : ℤ) - k
  let H := max γ₁ (max γ₂ γ₃)
  have hγ₁ : 0 < γ₁ := squarefreePart_pos (by omega)
  have hγ₂ : 0 < γ₂ := squarefreePart_pos (by omega)
  have hγ₃ : 0 < γ₃ := squarefreePart_pos (by omega)
  have hx₁ : 0 < x₁ := squareRootPart_pos (by omega)
  have hx₂ : 0 < x₂ := squareRootPart_pos (by omega)
  have hx₃ : 0 < x₃ := squareRootPart_pos (by omega)
  have hdec₁ : x₁ ^ 2 * γ₁ = n + i := squareRootPart_sq_mul_squarefreePart _
  have hdec₂ : x₂ ^ 2 * γ₂ = n + j := squareRootPart_sq_mul_squarefreePart _
  have hdec₃ : x₃ ^ 2 * γ₃ = n + k := squareRootPart_sq_mul_squarefreePart _
  have hPell : SimultaneousPellZ (γ₁ : ℤ) (γ₂ : ℤ) (γ₃ : ℤ)
      β₁₂ β₁₃ (x₁ : ℤ) (x₂ : ℤ) (x₃ : ℤ) := by
    simpa [γ₁, γ₂, γ₃, x₁, x₂, x₃, β₁₂, β₁₃] using
      three_shift_simultaneousPellZ hdec₁ hdec₂ hdec₃
  have hβ₁₂ : β₁₂ ≠ 0 := by
    dsimp [β₁₂]
    exact sub_ne_zero.mpr (by exact_mod_cast hij)
  have hβ₁₃ : β₁₃ ≠ 0 := by
    dsimp [β₁₃]
    exact sub_ne_zero.mpr (by exact_mod_cast hik)
  have hβ₂₃ : β₁₃ - β₁₂ ≠ 0 := by
    dsimp [β₁₃, β₁₂]
    have : (j : ℤ) ≠ k := by exact_mod_cast hjk
    omega
  have hiJ : i ≤ J := (Finset.mem_Icc.mp (hI (hK hi))).2
  have hjJ : j ≤ J := (Finset.mem_Icc.mp (hI (hK hj))).2
  have hkJ : k ≤ J := (Finset.mem_Icc.mp (hI (hK hk))).2
  have hJ₁₂ : β₁₂.natAbs ≤ 2 * J := by
    dsimp [β₁₂]
    calc
      ((i : ℤ) - j).natAbs ≤ (i : ℤ).natAbs + (j : ℤ).natAbs :=
        Int.natAbs_sub_le _ _
      _ ≤ 2 * J := by simp only [Int.natAbs_natCast]; omega
  have hJ₁₃ : β₁₃.natAbs ≤ 2 * J := by
    dsimp [β₁₃]
    calc
      ((i : ℤ) - k).natAbs ≤ (i : ℤ).natAbs + (k : ℤ).natAbs :=
        Int.natAbs_sub_le _ _
      _ ≤ 2 * J := by simp only [Int.natAbs_natCast]; omega
  have hJ₂₃ : (β₁₃ - β₁₂).natAbs ≤ 2 * J := by
    have heq : β₁₃ - β₁₂ = (j : ℤ) - k := by
      dsimp [β₁₃, β₁₂]
      ring
    rw [heq]
    calc
      ((j : ℤ) - k).natAbs ≤ (j : ℤ).natAbs + (k : ℤ).natAbs :=
        Int.natAbs_sub_le _ _
      _ ≤ 2 * J := by simp only [Int.natAbs_natCast]; omega
  have hγ₁H : γ₁ ≤ H := le_max_left _ _
  have hγ₂H : γ₂ ≤ H := le_trans (le_max_left _ _) (le_max_right _ _)
  have hγ₃H : γ₃ ≤ H := le_trans (le_max_right _ _) (le_max_right _ _)
  have hHpos : 0 < H := hγ₁.trans_le hγ₁H
  have hHpow : H ^ (K.card - 2) ≤
      J ^ (Nat.primeCounting J + K.card ^ 2 * Nat.log 2 J) := by
    apply max_three_pow_le_pell
    · simpa [γ₁] using hiPow
    · simpa [γ₂] using hjPow
    · simpa [γ₃] using hkPow
  refine ⟨H, hHpos, hHpow, ?_⟩
  exact simultaneousPell_loglog_le_degree_log hdec₁ hPell
    hβ₁₂ hβ₁₃ hβ₂₃ hJ₁₂ hJ₁₃ hJ₂₃
    hγ₁ hγ₂ hγ₃ hγ₁H hγ₂H hγ₃H hx₁ hx₂ hx₃ hnlarge

theorem sparse_pell_loglog_bound
    {n J : ℕ} {I K : Finset ℕ}
    (hnlarge : 1 < n) (hI : I ⊆ Finset.Icc 0 J) (hK : K ⊆ I)
    (hcard : 3 ≤ K.card) (hJ : 1 ≤ J)
    (hsquare : IsSquare (∏ a ∈ I, (n + a))) :
    ((K.card - 2 : ℕ) : ℝ) * Real.log (Real.log (n : ℝ)) ≤
      ((pellHeightDegree + 4 : ℕ) : ℝ) *
        (((K.card - 2 : ℕ) : ℝ) *
            Real.log ((4 * (J + 1) : ℕ) : ℝ) +
          ((Nat.primeCounting J + K.card ^ 2 * Nat.log 2 J : ℕ) : ℝ) *
            Real.log (J : ℝ)) := by
  obtain ⟨H, hH, hHpow, hroot⟩ :=
    sparse_pell_loglog_bound_data hnlarge hI hK hcard hJ hsquare
  let R := K.card - 2
  let E := Nat.primeCounting J + K.card ^ 2 * Nat.log 2 J
  let C : ℝ := ((pellHeightDegree + 4 : ℕ) : ℝ)
  have hR : 0 < R := by dsimp [R]; omega
  have hHone : 1 ≤ H := hH
  have hJpos : 0 < J := by omega
  have hHmul : H ≤ H * (J + 1) :=
    Nat.le_mul_of_pos_right H (by omega : 0 < J + 1)
  have hJmul : J + 1 ≤ H * (J + 1) := by
    simpa [Nat.mul_comm] using Nat.le_mul_of_pos_right (J + 1) hH
  have hsum : H + 2 * J + 2 ≤ 4 * H * (J + 1) := by
    calc
      H + 2 * J + 2 = H + 2 * (J + 1) := by omega
      _ ≤ H * (J + 1) + 2 * (H * (J + 1)) :=
        Nat.add_le_add hHmul (Nat.mul_le_mul_left 2 hJmul)
      _ ≤ 4 * (H * (J + 1)) := by omega
      _ = 4 * H * (J + 1) := by ring
  have hlogS : Real.log (H + 2 * J + 2 : ℕ) ≤
      Real.log (H : ℝ) + Real.log ((4 * (J + 1) : ℕ) : ℝ) := by
    calc
      Real.log (H + 2 * J + 2 : ℕ) ≤
          Real.log ((4 * H * (J + 1) : ℕ) : ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast hsum)
      _ = Real.log (H : ℝ) + Real.log ((4 * (J + 1) : ℕ) : ℝ) := by
        rw [show (4 * H * (J + 1) : ℕ) = H * (4 * (J + 1)) by ring,
          Nat.cast_mul, Real.log_mul]
        · exact_mod_cast hH.ne'
        · positivity
  have hleftPos : (0 : ℝ) < ((H ^ R : ℕ) : ℝ) := by positivity
  have hrightPos : (0 : ℝ) < ((J ^ E : ℕ) : ℝ) := by positivity
  have hpowlog : (R : ℝ) * Real.log (H : ℝ) ≤
      (E : ℝ) * Real.log (J : ℝ) := by
    have hlogmono : Real.log ((H ^ R : ℕ) : ℝ) ≤
        Real.log ((J ^ E : ℕ) : ℝ) := by
      apply Real.strictMonoOn_log.monotoneOn hleftPos hrightPos
      exact_mod_cast hHpow
    simp only [Nat.cast_pow] at hlogmono
    rw [Real.log_pow, Real.log_pow] at hlogmono
    exact hlogmono
  have hC : 0 ≤ C := by dsimp [C]; positivity
  calc
    (R : ℝ) * Real.log (Real.log (n : ℝ)) ≤
        (R : ℝ) * (C * Real.log (H + 2 * J + 2 : ℕ)) :=
      mul_le_mul_of_nonneg_left hroot (by positivity)
    _ = C * ((R : ℝ) * Real.log (H + 2 * J + 2 : ℕ)) := by ring
    _ ≤ C * ((R : ℝ) *
        (Real.log (H : ℝ) + Real.log ((4 * (J + 1) : ℕ) : ℝ))) := by
      gcongr
    _ = C * (((R : ℝ) * Real.log ((4 * (J + 1) : ℕ) : ℝ)) +
        ((R : ℝ) * Real.log (H : ℝ))) := by ring
    _ ≤ C * (((R : ℝ) * Real.log ((4 * (J + 1) : ℕ) : ℝ)) +
        ((E : ℝ) * Real.log (J : ℝ))) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add (le_refl _) hpowlog) hC
    _ = _ := by rfl

theorem minimal_pell_balancing_dichotomy
    {n r : ℕ} (hn : ¬IsSquare n) (hnlarge : 1 < n)
    (hr : 3 ≤ r) (htFour : 4 ≤ t n) :
    n ≤ (t n) ^ 2 ∨
      (∃ D : ℕ, 3 ≤ D ∧ D ≤ r ∧
        Real.log (Real.log (n : ℝ)) ≤
          ((pellHeightDegree + 4 : ℕ) : ℝ) *
            Real.log ((t n) ^ (D - 1) + 2 * t n + 2 : ℕ)) ∨
      ((r - 2 : ℕ) : ℝ) * Real.log (Real.log (n : ℝ)) ≤
        ((pellHeightDegree + 4 : ℕ) : ℝ) *
          (((r - 2 : ℕ) : ℝ) *
              Real.log ((4 * (t n + 1) : ℕ) : ℝ) +
            ((Nat.primeCounting (t n) + r ^ 2 * Nat.log 2 (t n) : ℕ) : ℝ) *
              Real.log (t n : ℝ)) := by
  obtain ⟨I, y, hI, h0, ht, hcard, hsq⟩ := exists_minimal_curve_shifts hn
  by_cases htwo : I.card = 2
  · exact Or.inl (minimal_curve_card_two_bound hn h0 ht htwo hsq)
  have hthree : 3 ≤ I.card := by omega
  by_cases hfar : 4 * t n < n
  · right
    by_cases hsmall : I.card ≤ r
    · left
      exact ⟨I.card, hthree, hsmall,
        direct_pell_loglog_bound (by omega) hnlarge hfar hI hthree
          ⟨y, by simpa [pow_two] using hsq.symm⟩⟩
    · right
      have hrle : r ≤ I.card := by omega
      obtain ⟨K, hKI, hKcard⟩ := Finset.exists_subset_card_eq hrle
      have hsquare : IsSquare (∏ a ∈ I, (n + a)) :=
        ⟨y, by simpa [pow_two] using hsq.symm⟩
      have hsparse := sparse_pell_loglog_bound hnlarge hI hKI
        (by omega : 3 ≤ K.card) (by omega : 1 ≤ t n) hsquare
      simpa only [hKcard] using hsparse
  · left
    have hnFour : n ≤ 4 * t n := by omega
    have hFourSq : 4 * t n ≤ (t n) ^ 2 := by
      simpa [pow_two] using Nat.mul_le_mul_right (t n) htFour
    exact hnFour.trans hFourSq

noncomputable def pellBalanceConstant : ℝ :=
  40 * ((pellHeightDegree + 4 : ℕ) : ℝ)

lemma pellBalanceConstant_pos : 0 < pellBalanceConstant := by
  dsimp [pellBalanceConstant]
  positivity

lemma direct_pell_expression_le_balance
    {J D : ℕ} (hJ : 2 ≤ J) (hD : 3 ≤ D) (hDJ : D ≤ J)
    (hDscale : (D : ℝ) ≤ lowerBalanceScale J) :
    ((pellHeightDegree + 4 : ℕ) : ℝ) *
        Real.log (J ^ (D - 1) + 2 * J + 2 : ℕ) ≤
      pellBalanceConstant * lowerBalanceMagnitude J := by
  let C : ℝ := ((pellHeightDegree + 4 : ℕ) : ℝ)
  let S := lowerBalanceScale J
  have hJpos : 0 < J := by omega
  have hlogJ : 0 < Real.log (J : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < J by omega))
  have hpowA : J ^ (D - 1) ≤ J ^ (D + 2) :=
    Nat.pow_le_pow_right hJpos (by omega)
  have hlin : 2 * J + 2 ≤ J ^ 3 := by
    have hfour : 4 ≤ J ^ 2 := by
      simpa using Nat.pow_le_pow_left hJ 2
    have hthree : 3 ≤ J ^ 2 := by omega
    calc
      2 * J + 2 ≤ 3 * J := by omega
      _ ≤ J ^ 2 * J := Nat.mul_le_mul_right J hthree
      _ = J ^ 3 := by ring
  have hpowB : J ^ 3 ≤ J ^ (D + 2) :=
    Nat.pow_le_pow_right hJpos (by omega)
  have hsum : J ^ (D - 1) + 2 * J + 2 ≤ J ^ (D + 3) := by
    calc
      J ^ (D - 1) + 2 * J + 2 = J ^ (D - 1) + (2 * J + 2) := by omega
      _ ≤ J ^ (D + 2) + J ^ (D + 2) := Nat.add_le_add hpowA (hlin.trans hpowB)
      _ = 2 * J ^ (D + 2) := by ring
      _ ≤ J * J ^ (D + 2) := Nat.mul_le_mul_right _ hJ
      _ = J ^ (D + 3) := by rw [← pow_succ']
  have hlog : Real.log (J ^ (D - 1) + 2 * J + 2 : ℕ) ≤
      ((D + 3 : ℕ) : ℝ) * Real.log (J : ℝ) := by
    calc
      Real.log (J ^ (D - 1) + 2 * J + 2 : ℕ) ≤
          Real.log ((J ^ (D + 3) : ℕ) : ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast hsum)
      _ = ((D + 3 : ℕ) : ℝ) * Real.log (J : ℝ) := by
        simp only [Nat.cast_pow]
        rw [Real.log_pow]
  have hscaleOne : (1 : ℝ) ≤ S := by
    exact (show (1 : ℝ) ≤ D by exact_mod_cast (by omega : 1 ≤ D)).trans hDscale
  have hscalePow : S ≤ S ^ 5 := by
    calc
      S = S * 1 := by ring
      _ ≤ S * S ^ 4 := by
        apply mul_le_mul_of_nonneg_left (one_le_pow₀ hscaleOne) (by positivity)
      _ = S ^ 5 := by ring
  have hDscale' : ((D + 3 : ℕ) : ℝ) ≤ 2 * S := by
    have hDthree : ((D + 3 : ℕ) : ℝ) ≤ 2 * (D : ℝ) := by
      exact_mod_cast (show D + 3 ≤ 2 * D by omega)
    exact hDthree.trans (mul_le_mul_of_nonneg_left hDscale (by norm_num))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  calc
    C * Real.log (J ^ (D - 1) + 2 * J + 2 : ℕ) ≤
        C * (((D + 3 : ℕ) : ℝ) * Real.log (J : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog hC
    _ ≤ C * ((2 * S ^ 5) * Real.log (J : ℝ)) := by
      gcongr
      exact hDscale'.trans (mul_le_mul_of_nonneg_left hscalePow (by norm_num))
    _ ≤ (40 * C) * (S ^ 5 * Real.log (J : ℝ)) := by
      have hnonneg : 0 ≤ C * (S ^ 5 * Real.log (J : ℝ)) := by positivity
      nlinarith
    _ = pellBalanceConstant * lowerBalanceMagnitude J := by
      simp only [pellBalanceConstant, lowerBalanceMagnitude, C, S]

lemma sparse_pell_expression_le_balance_eventually :
    ∀ᶠ J : ℕ in Filter.atTop, ∀ L : ℝ,
      (((lowerBalanceCutoff J - 2 : ℕ) : ℝ) * L ≤
        ((pellHeightDegree + 4 : ℕ) : ℝ) *
          (((lowerBalanceCutoff J - 2 : ℕ) : ℝ) *
              Real.log ((4 * (J + 1) : ℕ) : ℝ) +
            ((Nat.primeCounting J + lowerBalanceCutoff J ^ 2 *
                Nat.log 2 J : ℕ) : ℝ) * Real.log (J : ℝ))) →
        L ≤ pellBalanceConstant * lowerBalanceMagnitude J := by
  have hscaleOne := lowerBalanceScale_tendsto_atTop.eventually
    (Filter.eventually_ge_atTop 1)
  have hlogTop : Filter.Tendsto (fun J : ℕ ↦ Real.log (J : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogOne := hlogTop.eventually (Filter.eventually_ge_atTop 1)
  filter_upwards [eventually_lowerBalanceCutoff_bounds,
    eventually_log_le_lowerBalanceScale_sq,
    eventually_primeCounting_le_four_mul_div_log,
    hscaleOne, hlogOne, Filter.eventually_ge_atTop 3] with
      J hcut hlogScale hpi hscaleOne hlogOne hJ
  intro L hSparse
  let r := lowerBalanceCutoff J
  let R := r - 2
  let C : ℝ := ((pellHeightDegree + 4 : ℕ) : ℝ)
  have hr3 : 3 ≤ r := hcut.1
  have hRpos : (0 : ℝ) < (R : ℝ) := by
    exact_mod_cast (show 0 < R by dsimp [R]; omega)
  have hlogPos : 0 < Real.log (J : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < J by omega))
  have hscaleNonneg : 0 ≤ lowerBalanceScale J := hscaleOne.trans' zero_le_one
  have hmagNonneg : 0 ≤ lowerBalanceMagnitude J := by
    rw [lowerBalanceMagnitude]
    positivity
  have hrToScale : (r : ℝ) ≤ lowerBalanceScale J := by
    simpa [r] using hcut.2.2
  have hscaleToR : lowerBalanceScale J ≤ 6 * (R : ℝ) := by
    have hlow : lowerBalanceScale J / 2 ≤ (r : ℝ) := by
      simpa [r] using hcut.2.1
    have hrthree : (r : ℝ) ≤ 3 * (R : ℝ) := by
      exact_mod_cast (show r ≤ 3 * R by dsimp [R]; omega)
    nlinarith
  have hJbalance : (J : ℝ) ≤
      6 * (R : ℝ) * lowerBalanceMagnitude J := by
    calc
      (J : ℝ) = lowerBalanceScale J * lowerBalanceMagnitude J :=
        (lowerBalanceScale_mul_magnitude (by omega : 1 < J)).symm
      _ ≤ (6 * (R : ℝ)) * lowerBalanceMagnitude J :=
        mul_le_mul_of_nonneg_right hscaleToR hmagNonneg
  have hlogMag : Real.log (J : ℝ) ≤ lowerBalanceMagnitude J := by
    rw [lowerBalanceMagnitude]
    have hpowOne : (1 : ℝ) ≤ lowerBalanceScale J ^ 5 :=
      one_le_pow₀ hscaleOne
    nlinarith [mul_le_mul_of_nonneg_right hpowOne hlogPos.le]
  have hpiLog : (Nat.primeCounting J : ℝ) * Real.log (J : ℝ) ≤
      4 * (J : ℝ) := by
    calc
      (Nat.primeCounting J : ℝ) * Real.log (J : ℝ) ≤
          (4 * (J : ℝ) / Real.log (J : ℝ)) * Real.log (J : ℝ) :=
        mul_le_mul_of_nonneg_right hpi hlogPos.le
      _ = 4 * (J : ℝ) := by field_simp
  have hlogSq : Real.log (J : ℝ) ^ 2 ≤ lowerBalanceScale J ^ 4 := by
    calc
      Real.log (J : ℝ) ^ 2 ≤ (lowerBalanceScale J ^ 2) ^ 2 :=
        pow_le_pow_left₀ hlogPos.le hlogScale 2
      _ = lowerBalanceScale J ^ 4 := by ring
  have hrLogSq : (r : ℝ) * Real.log (J : ℝ) ^ 2 ≤
      lowerBalanceScale J ^ 5 := by
    calc
      (r : ℝ) * Real.log (J : ℝ) ^ 2 ≤
          lowerBalanceScale J * lowerBalanceScale J ^ 4 :=
        mul_le_mul hrToScale hlogSq (sq_nonneg _) hscaleNonneg
      _ = lowerBalanceScale J ^ 5 := by ring
  have hrThree : (r : ℝ) ≤ 3 * (R : ℝ) := by
    exact_mod_cast (show r ≤ 3 * R by dsimp [R]; omega)
  have hscaleFiveMag : lowerBalanceScale J ^ 5 ≤ lowerBalanceMagnitude J := by
    rw [lowerBalanceMagnitude]
    exact le_mul_of_one_le_right (by positivity) hlogOne
  have hNatLog := natLog_two_le_two_mul_log (show 2 ≤ J by omega)
  have hA : (R : ℝ) * Real.log (4 * ((J : ℝ) + 1)) ≤
      4 * (R : ℝ) * lowerBalanceMagnitude J := by
    have hlogFour : Real.log (4 * ((J : ℝ) + 1)) ≤
        4 * Real.log (J : ℝ) := by
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
        using log_four_mul_succ_le_four_mul_log (show 2 ≤ J by omega)
    calc
      (R : ℝ) * Real.log (4 * ((J : ℝ) + 1)) ≤
          (R : ℝ) * (4 * Real.log (J : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogFour (by positivity)
      _ ≤ 4 * (R : ℝ) * lowerBalanceMagnitude J := by
        nlinarith [mul_le_mul_of_nonneg_left hlogMag
          (show 0 ≤ 4 * (R : ℝ) by positivity)]
  have hB : (Nat.primeCounting J : ℝ) * Real.log (J : ℝ) ≤
      24 * (R : ℝ) * lowerBalanceMagnitude J := by
    calc
      (Nat.primeCounting J : ℝ) * Real.log (J : ℝ) ≤
          4 * (J : ℝ) := hpiLog
      _ ≤ 24 * (R : ℝ) * lowerBalanceMagnitude J := by nlinarith
  have hcore : (r : ℝ) ^ 2 * (Nat.log 2 J : ℝ) *
      Real.log (J : ℝ) ≤ 2 * (r : ℝ) * lowerBalanceScale J ^ 5 := by
    calc
      (r : ℝ) ^ 2 * (Nat.log 2 J : ℝ) * Real.log (J : ℝ) ≤
          (r : ℝ) ^ 2 * (2 * Real.log (J : ℝ)) *
            Real.log (J : ℝ) := by gcongr
      _ = 2 * (r : ℝ) * ((r : ℝ) * Real.log (J : ℝ) ^ 2) := by ring
      _ ≤ 2 * (r : ℝ) * lowerBalanceScale J ^ 5 := by gcongr
  have hCterm : (r : ℝ) ^ 2 * (Nat.log 2 J : ℝ) *
      Real.log (J : ℝ) ≤ 6 * (R : ℝ) * lowerBalanceMagnitude J := by
    calc
      _ ≤ 2 * (r : ℝ) * lowerBalanceScale J ^ 5 := hcore
      _ ≤ 6 * (R : ℝ) * lowerBalanceScale J ^ 5 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith
      _ ≤ 6 * (R : ℝ) * lowerBalanceMagnitude J := by gcongr
  have hInner :
      (R : ℝ) * Real.log (4 * ((J : ℝ) + 1)) +
          ((Nat.primeCounting J : ℝ) +
            (r : ℝ) ^ 2 * (Nat.log 2 J : ℝ)) * Real.log (J : ℝ) ≤
        34 * (R : ℝ) * lowerBalanceMagnitude J := by
    calc
      _ = (R : ℝ) * Real.log (4 * ((J : ℝ) + 1)) +
          ((Nat.primeCounting J : ℝ) * Real.log (J : ℝ)) +
          ((r : ℝ) ^ 2 * (Nat.log 2 J : ℝ) * Real.log (J : ℝ)) := by ring
      _ ≤ 4 * (R : ℝ) * lowerBalanceMagnitude J +
          24 * (R : ℝ) * lowerBalanceMagnitude J +
          6 * (R : ℝ) * lowerBalanceMagnitude J :=
        add_le_add (add_le_add hA hB) hCterm
      _ = 34 * (R : ℝ) * lowerBalanceMagnitude J := by ring
  have hSparse' : (R : ℝ) * L ≤ C *
      ((R : ℝ) * Real.log (4 * ((J : ℝ) + 1)) +
        ((Nat.primeCounting J : ℝ) +
          (r : ℝ) ^ 2 * (Nat.log 2 J : ℝ)) * Real.log (J : ℝ)) := by
    simpa only [r, R, C, Nat.cast_sub (by omega : 2 ≤ lowerBalanceCutoff J),
      Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using hSparse
  have hCnonneg : 0 ≤ C := by dsimp [C]; positivity
  have hRhs : C *
      ((R : ℝ) * Real.log (4 * ((J : ℝ) + 1)) +
        ((Nat.primeCounting J : ℝ) +
          (r : ℝ) ^ 2 * (Nat.log 2 J : ℝ)) * Real.log (J : ℝ)) ≤
      (R : ℝ) * (pellBalanceConstant * lowerBalanceMagnitude J) := by
    calc
      _ ≤ C * (34 * (R : ℝ) * lowerBalanceMagnitude J) :=
        mul_le_mul_of_nonneg_left hInner hCnonneg
      _ ≤ C * (40 * (R : ℝ) * lowerBalanceMagnitude J) := by
        gcongr
        norm_num
      _ = (R : ℝ) * (pellBalanceConstant * lowerBalanceMagnitude J) := by
        simp only [pellBalanceConstant, C]
        ring
  exact le_of_mul_le_mul_left (hSparse'.trans hRhs) hRpos

theorem eventual_minimal_loglog_balance_pell :
    ∀ᶠ J : ℕ in Filter.atTop, ∀ n : ℕ,
      ¬IsSquare n → 1 < n → t n = J →
        n ≤ J ^ 2 ∨
          Real.log (Real.log (n : ℝ)) ≤
            pellBalanceConstant * lowerBalanceMagnitude J := by
  filter_upwards [eventually_lowerBalanceCutoff_bounds,
    eventually_lowerBalanceCutoff_le_self,
    sparse_pell_expression_le_balance_eventually,
    Filter.eventually_ge_atTop 4] with J hcut hcutJ hsparse hJ
  intro n hn hnlarge ht
  have htFour : 4 ≤ t n := by simpa only [ht] using hJ
  have hdich := minimal_pell_balancing_dichotomy hn hnlarge hcut.1 htFour
  rcases hdich with hquad | hdirect | hsparseRaw
  · left
    simpa only [ht] using hquad
  · right
    obtain ⟨D, hDthree, hDcut, hraw⟩ := hdirect
    have hDJ : D ≤ J := hDcut.trans hcutJ
    have hDscale : (D : ℝ) ≤ lowerBalanceScale J := by
      exact (Nat.cast_le.mpr hDcut).trans hcut.2.2
    have hbound := direct_pell_expression_le_balance
      (by omega : 2 ≤ J) hDthree hDJ hDscale
    rw [ht] at hraw
    exact hraw.trans hbound
  · right
    rw [ht] at hsparseRaw
    exact hsparse (Real.log (Real.log (n : ℝ))) hsparseRaw

theorem minimal_direct_pell_loglog_dichotomy_unconditional
    {n : ℕ} (hn : ¬IsSquare n) (hnlarge : 1 < n) :
    n ≤ 4 * t n ∨ n ≤ (t n) ^ 2 ∨
      ∃ D : ℕ, 3 ≤ D ∧ D ≤ t n + 1 ∧
        Real.log (Real.log (n : ℝ)) ≤
          ((pellHeightDegree + 4 : ℕ) : ℝ) *
            Real.log ((t n) ^ (D - 1) + 2 * t n + 2 : ℕ) := by
  obtain ⟨I, y, hI, h0, ht, hcard, hsq⟩ := exists_minimal_curve_shifts hn
  by_cases htwo : I.card = 2
  · exact Or.inr (Or.inl (minimal_curve_card_two_bound hn h0 ht htwo hsq))
  have hthree : 3 ≤ I.card := by omega
  have hDle : I.card ≤ t n + 1 := by
    have hc := Finset.card_le_card hI
    simpa using hc
  by_cases hfar : 4 * t n < n
  · exact Or.inr (Or.inr ⟨I.card, hthree, hDle,
      direct_pell_loglog_bound (by omega) hnlarge hfar hI hthree
        ⟨y, by simpa [pow_two] using hsq.symm⟩⟩)
  · exact Or.inl (by omega)

theorem eventually_t_ge_of_not_square_pell (B : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop, ¬IsSquare n → B ≤ t n := by
  let M := B + 3
  let C : ℝ := ((pellHeightDegree + 4 : ℕ) : ℝ)
  let K : ℝ := C * Real.log (M ^ M + 2 * M + 2 : ℕ)
  have hloglogTop : Filter.Tendsto
      (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlogLarge := hloglogTop.eventually (Filter.eventually_gt_atTop K)
  filter_upwards [hlogLarge, Filter.eventually_gt_atTop (M ^ 2),
    Filter.eventually_gt_atTop (4 * M)] with n hlogLarge hnM hnFour
  intro hn
  by_contra hBt
  have htB : t n < B := by omega
  have hnlarge : 1 < n := by
    by_contra hnle
    interval_cases n <;> simp_all only [IsSquare.zero, IsSquare.one, not_true_eq_false]
  rcases minimal_direct_pell_loglog_dichotomy_unconditional hn hnlarge with
    hnear | hquad | ⟨D, hDthree, hDt, hroot⟩
  · have htM : t n ≤ M := by dsimp [M]; omega
    have hfour : 4 * t n ≤ 4 * M := Nat.mul_le_mul_left 4 htM
    omega
  · have htM : t n < M := by dsimp [M]; omega
    have hsq : (t n) ^ 2 < M ^ 2 := Nat.pow_lt_pow_left htM (by decide)
    omega
  · have htM : t n ≤ M := by dsimp [M]; omega
    have hDM : D - 1 ≤ M := by dsimp [M]; omega
    have hMpos : 0 < M := by dsimp [M]; omega
    have hpow : (t n) ^ (D - 1) ≤ M ^ M := by
      exact (Nat.pow_le_pow_left htM _).trans (Nat.pow_le_pow_right hMpos hDM)
    have harg : (t n) ^ (D - 1) + 2 * t n + 2 ≤ M ^ M + 2 * M + 2 := by
      omega
    have hlog : Real.log ((t n) ^ (D - 1) + 2 * t n + 2 : ℕ) ≤
        Real.log (M ^ M + 2 * M + 2 : ℕ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast harg)
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have hroot' : Real.log (Real.log (n : ℝ)) ≤ K := by
      exact hroot.trans (by
        dsimp [K, C]
        exact mul_le_mul_of_nonneg_left hlog hC)
    exact (not_le_of_gt hlogLarge) hroot'

theorem eventual_minimal_loglog_balance_on_n_pell :
    ∀ᶠ n : ℕ in Filter.atTop, ¬IsSquare n →
      n ≤ (t n) ^ 2 ∨
        Real.log (Real.log (n : ℝ)) ≤
          pellBalanceConstant * lowerBalanceMagnitude (t n) := by
  have hbalance := eventual_minimal_loglog_balance_pell
  rw [Filter.eventually_atTop] at hbalance
  obtain ⟨J₀, hJ₀⟩ := hbalance
  filter_upwards [eventually_t_ge_of_not_square_pell J₀,
    Filter.eventually_ge_atTop 2] with n htLarge hn2
  intro hn
  exact hJ₀ (t n) (htLarge hn) n hn (by omega) rfl

noncomputable def pellLowerBoundConstant : ℝ :=
  1 / (2 * pellBalanceConstant ^ 6)

lemma pellLowerBoundConstant_pos : 0 < pellLowerBoundConstant := by
  rw [pellLowerBoundConstant]
  exact div_pos zero_lt_one
    (mul_pos (by norm_num) (pow_pos pellBalanceConstant_pos _))

lemma pellLowerBoundConstant_le_one : pellLowerBoundConstant ≤ 1 := by
  have hAone : (1 : ℝ) ≤ pellBalanceConstant := by
    rw [pellBalanceConstant]
    have hdegree : (1 : ℝ) ≤ ((pellHeightDegree + 4 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ pellHeightDegree + 4 by omega)
    nlinarith
  rw [pellLowerBoundConstant]
  have hdenom : (1 : ℝ) ≤ 2 * pellBalanceConstant ^ 6 := by
    have hp : (1 : ℝ) ≤ pellBalanceConstant ^ 6 := one_le_pow₀ hAone
    nlinarith
  exact (div_le_one₀ (by positivity)).2 hdenom

lemma lowerLogShape_le_of_pell_balance {L J A : ℝ}
    (hL : 1 < L) (hlogL : 1 ≤ Real.log L) (hJ : 1 < J)
    (hJL : J ≤ L ^ 2)
    (hAnonneg : 0 ≤ A) (hbalance : L ≤ pellBalanceConstant * A)
    (hmagPow : A ^ 6 = J ^ 5 * Real.log J) :
    pellLowerBoundConstant * lowerLogShape L ≤ J := by
  have hJpos : 0 < J := by linarith
  have hlogJ : 0 < Real.log J := Real.log_pos hJ
  have hLsix : L ^ 6 ≤
      pellBalanceConstant ^ 6 * (J ^ 5 * Real.log J) := by
    have hp := pow_le_pow_left₀ (by linarith : 0 ≤ L) hbalance 6
    rw [mul_pow, hmagPow] at hp
    exact hp
  have hlogJLe : Real.log J ≤ 2 * Real.log L := by
    calc
      Real.log J ≤ Real.log (L ^ 2) := Real.log_le_log hJpos hJL
      _ = 2 * Real.log L := by rw [Real.log_pow]; norm_num
  have hLsix' : L ^ 6 ≤
      2 * pellBalanceConstant ^ 6 * J ^ 5 * Real.log L := by
    calc
      L ^ 6 ≤ pellBalanceConstant ^ 6 * (J ^ 5 * Real.log J) := hLsix
      _ ≤ pellBalanceConstant ^ 6 * (J ^ 5 * (2 * Real.log L)) := by
        gcongr
      _ = 2 * pellBalanceConstant ^ 6 * J ^ 5 * Real.log L := by ring
  have hcPos : 0 < pellLowerBoundConstant := pellLowerBoundConstant_pos
  have hcOne : pellLowerBoundConstant ≤ 1 := pellLowerBoundConstant_le_one
  have hcCancel : pellLowerBoundConstant *
      (2 * pellBalanceConstant ^ 6) = 1 := by
    rw [pellLowerBoundConstant]
    field_simp [pellBalanceConstant_pos.ne']
  have hcL : pellLowerBoundConstant * L ^ 6 ≤ J ^ 5 * Real.log L := by
    calc
      pellLowerBoundConstant * L ^ 6 ≤ pellLowerBoundConstant *
          (2 * pellBalanceConstant ^ 6 * J ^ 5 * Real.log L) :=
        mul_le_mul_of_nonneg_left hLsix' hcPos.le
      _ = (pellLowerBoundConstant * (2 * pellBalanceConstant ^ 6)) *
          (J ^ 5 * Real.log L) := by ring
      _ = J ^ 5 * Real.log L := by rw [hcCancel, one_mul]
  have hcPow : pellLowerBoundConstant ^ 5 ≤ pellLowerBoundConstant := by
    simpa only [pow_one] using
      (pow_le_pow_of_le_one hcPos.le hcOne (by omega : 1 ≤ (5 : ℕ)))
  have hbase : 0 ≤ L ^ 6 / Real.log L :=
    div_nonneg (by positivity) (Real.log_pos hL).le
  have htargetPow : (pellLowerBoundConstant * lowerLogShape L) ^ 5 ≤ J ^ 5 := by
    rw [mul_pow, lowerLogShape_pow_five hL]
    calc
      pellLowerBoundConstant ^ 5 * (L ^ 6 / Real.log L) ≤
          pellLowerBoundConstant * (L ^ 6 / Real.log L) :=
        mul_le_mul_of_nonneg_right hcPow hbase
      _ ≤ J ^ 5 := by
        rw [← mul_div_assoc]
        exact (div_le_iff₀ (Real.log_pos hL)).2 (by simpa [mul_assoc] using hcL)
  exact le_of_pow_le_pow_left₀ (by norm_num : (5 : ℕ) ≠ 0) hJpos.le htargetPow

theorem erdos841_lower_bound :
    ∀ᶠ n : ℕ in Filter.atTop, ¬IsSquare n →
      pellLowerBoundConstant * lowerBoundShape n ≤ (t n : ℝ) := by
  filter_upwards [eventual_minimal_loglog_balance_on_n_pell,
    eventually_lowerBoundShape_inputs,
    eventually_t_ge_of_not_square_pell 2] with n hbalance hinput htTwo
  intro hn
  have hbal := hbalance hn
  have ht := htTwo hn
  let L := Real.log (Real.log (n : ℝ))
  have hL : 1 < L := hinput.1
  have hlogL : 1 ≤ Real.log L := by simpa [L] using hinput.2.1
  have hshape : lowerBoundShape n = lowerLogShape L := rfl
  have hshapeSq : lowerLogShape L ≤ L ^ 2 :=
    lowerLogShape_le_sq hL hlogL
  have hcPos : 0 < pellLowerBoundConstant := pellLowerBoundConstant_pos
  have hcOne : pellLowerBoundConstant ≤ 1 := pellLowerBoundConstant_le_one
  have hshapeNonneg : 0 ≤ lowerLogShape L := lowerLogShape_nonneg hL
  have hcrude : pellLowerBoundConstant * lowerLogShape L ≤ L ^ 2 := by
    exact (mul_le_mul_of_nonneg_right hcOne hshapeNonneg).trans (by simpa using hshapeSq)
  rcases hbal with hquad | hheightBal
  · rw [hshape]
    have hpow : (L ^ 2) ^ 2 ≤ ((t n : ℝ) ^ 2) := by
      calc
        (L ^ 2) ^ 2 = L ^ 4 := by ring
        _ ≤ (n : ℝ) := hinput.2.2
        _ ≤ ((t n : ℝ) ^ 2) := by exact_mod_cast hquad
    have hLsq : L ^ 2 ≤ (t n : ℝ) :=
      le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) (by positivity) hpow
    exact hcrude.trans hLsq
  · rw [hshape]
    by_cases hsmall : (t n : ℝ) ≤ L ^ 2
    · apply lowerLogShape_le_of_pell_balance
          (A := lowerBalanceMagnitude (t n)) hL hlogL
          (by exact_mod_cast (show 1 < t n by omega)) hsmall
      · rw [lowerBalanceMagnitude]
        have hs : 0 ≤ lowerBalanceScale (t n) := by
          rw [lowerBalanceScale]
          apply Real.rpow_nonneg
          exact div_nonneg (by positivity)
            (Real.log_nonneg (by exact_mod_cast (show 1 ≤ t n by omega)))
        exact mul_nonneg (pow_nonneg hs _)
          (Real.log_nonneg (by exact_mod_cast (show 1 ≤ t n by omega)))
      · exact hheightBal
      · exact lowerBalanceMagnitude_pow_six (by omega : 1 < t n)
    · exact hcrude.trans (lt_of_not_ge hsmall).le

theorem erdos841_lower_bound_explicit :
    ∀ᶠ n : ℕ in Filter.atTop, ¬IsSquare n →
      pellLowerBoundConstant *
          (Real.log (Real.log (n : ℝ)) ^ ((6 : ℝ) / 5) *
            Real.log (Real.log (Real.log (n : ℝ))) ^ (-((1 : ℝ) / 5))) ≤
        (t n : ℝ) := by
  filter_upwards [erdos841_lower_bound,
    eventually_lowerBoundShape_inputs] with n hbound hinput
  intro hn
  have hb := hbound hn
  rw [lowerBoundShape, lowerLogShape_eq hinput.1] at hb
  exact hb

/-- The complete formal resolution of Erdős Problem 841: the exact
large-prime branch, the complementary square-root estimate, the BPZ
distribution theorem, the `x^(1-o(1))` family of small values, and the
unconditional pointwise lower bound. -/
theorem erdos841_complete_resolution :
    (∀ n : ℕ, 1 < n →
      Real.sqrt (2 * (n : ℝ)) + 1 < (largestPrimeFactor n : ℝ) →
        t n = largestPrimeFactor n) ∧
    (∀ n : ℕ,
      (largestPrimeFactor n : ℝ) ≤ Real.sqrt (2 * (n : ℝ)) + 1 →
        (t n : ℝ) ≤ 40 * Real.sqrt (n : ℝ)) ∧
    (∀ c : ℝ, 0 < c → c ≤ 1 →
      Filter.Tendsto
        (fun x : ℕ ↦
          (((movingSmallTUpTo x c).card : ℝ) -
            ((movingSmoothUpTo x c).card : ℝ)) / (x : ℝ))
        Filter.atTop (nhds 0)) ∧
    (Filter.Tendsto
        (fun x : ℕ ↦ Real.log ((manySmallUpTo x).card : ℝ) /
          Real.log (x : ℝ))
        Filter.atTop (nhds 1) ∧
      ∀ x n : ℕ, n ∈ manySmallUpTo x ↔
        1 ≤ n ∧ n ≤ x ∧
          (t n : ℝ) ≤ Real.exp
            (20 * Real.sqrt (Real.log n * Real.log (Real.log n)))) ∧
    (∀ᶠ n : ℕ in Filter.atTop, ¬IsSquare n →
      pellLowerBoundConstant *
          (Real.log (Real.log (n : ℝ)) ^ ((6 : ℝ) / 5) *
            Real.log (Real.log (Real.log (n : ℝ))) ^ (-((1 : ℝ) / 5))) ≤
        (t n : ℝ)) := by
  refine ⟨?_, ?_, erdos841_distributional_resolution,
    erdos841_many_small_values_global, erdos841_lower_bound_explicit⟩
  · intro n hn hlarge
    exact erdos841 hn hlarge
  · intro n hsmall
    exact erdos841_selfridge_sqrt_bound_all hsmall

end Erdos841
