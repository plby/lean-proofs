import Util.TaoTeravainen.PrimePowerTruncation

/-!
# Tao--Teräväinen: truncated prime-power moments

This is the finite moment calculation for the proper prime powers below a
chosen radius.  The truncation is what keeps the interval error summable.
-/

noncomputable section

open scoped ArithmeticFunction.omega ArithmeticFunction.Omega BigOperators

namespace TaoTeravainen

local instance primePowerTruncatedMomentDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

def truncatedPrimePowerSecondMoment (K J k : ℕ) : ℝ :=
  Erdos248.weightedSecondMoment (sieveInterval K) (Erdos248.sieveWeight K)
    (fun n => (truncatedProperPrimePowerCount J (n + k) : ℝ))

def weightedTruncatedPrimePowerBadMass (K J T k : ℕ) : ℝ :=
  Erdos248.weightedMass (sieveInterval K) (Erdos248.sieveWeight K)
    (fun n => T * k < truncatedProperPrimePowerCount J (n + k))

theorem truncatedProperPrimePowerCount_cast_eq_indicatorSum (J n : ℕ) :
    (truncatedProperPrimePowerCount J n : ℝ) =
      ∑ pa ∈ properPrimePowerIndices J,
        Erdos248.realIndicator (pa.1 ^ pa.2 ∣ n) := by
  unfold truncatedProperPrimePowerCount
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro pa hpa
  by_cases h : pa.1 ^ pa.2 ∣ n <;>
    simp [h, Erdos248.realIndicator]

theorem sq_mul_weightedTruncatedPrimePowerBadMass_le_secondMoment
    (K J T k : ℕ) :
    ((T * k : ℕ) : ℝ) ^ 2 *
        weightedTruncatedPrimePowerBadMass K J T k ≤
      truncatedPrimePowerSecondMoment K J k := by
  let s := sieveInterval K
  let w := Erdos248.sieveWeight K
  let Z : ℕ → ℝ := fun n => (truncatedProperPrimePowerCount J (n + k) : ℝ)
  have hsubset : weightedTruncatedPrimePowerBadMass K J T k ≤
      Erdos248.weightedMass s w
        (fun n => ((T * k : ℕ) : ℝ) ≤ |Z n|) := by
    unfold weightedTruncatedPrimePowerBadMass Erdos248.weightedMass
      Erdos248.weightedSum
    apply Finset.sum_le_sum
    intro n hn
    apply mul_le_mul_of_nonneg_left _ (Erdos248.sieveWeight_nonneg K n)
    change Erdos248.realIndicator
        (T * k < truncatedProperPrimePowerCount J (n + k)) ≤
      Erdos248.realIndicator (((T * k : ℕ) : ℝ) ≤ |Z n|)
    by_cases hbad : T * k < truncatedProperPrimePowerCount J (n + k)
    · rw [Erdos248.realIndicator_of_true hbad,
        Erdos248.realIndicator_of_true]
      dsimp [Z]
      rw [abs_of_nonneg (by positivity)]
      exact_mod_cast hbad.le
    · rw [Erdos248.realIndicator_of_false hbad]
      exact Erdos248.realIndicator_nonneg _
  have hmarkov := Erdos248.sq_mul_weightedMass_threshold_abs_le_secondMoment
    (s := s) (w := w) (Z := Z) (t := ((T * k : ℕ) : ℝ))
    (by positivity) (by intro n hn; exact Erdos248.sieveWeight_nonneg K n)
  calc
    ((T * k : ℕ) : ℝ) ^ 2 *
        weightedTruncatedPrimePowerBadMass K J T k ≤
        ((T * k : ℕ) : ℝ) ^ 2 *
          Erdos248.weightedMass s w
            (fun n => ((T * k : ℕ) : ℝ) ≤ |Z n|) :=
      mul_le_mul_of_nonneg_left hsubset (by positivity)
    _ ≤ Erdos248.weightedSecondMoment s w Z := hmarkov
    _ = truncatedPrimePowerSecondMoment K J k := rfl

theorem truncatedPrimePowerSecondMoment_eq_doublePairEventMass
    (K J k : ℕ) :
    truncatedPrimePowerSecondMoment K J k =
      ∑ pa ∈ properPrimePowerIndices J,
        ∑ qb ∈ properPrimePowerIndices J,
          primePowerPairEventMass K k pa.1 pa.2 qb.1 qb.2 := by
  let I := properPrimePowerIndices J
  unfold truncatedPrimePowerSecondMoment Erdos248.weightedSecondMoment
    Erdos248.weightedMoment Erdos248.weightedSum
  calc
    (∑ n ∈ sieveInterval K,
      Erdos248.sieveWeight K n *
        (truncatedProperPrimePowerCount J (n + k) : ℝ) ^ 2) =
        ∑ n ∈ sieveInterval K,
          Erdos248.sieveWeight K n *
            (∑ pa ∈ I,
              Erdos248.realIndicator (pa.1 ^ pa.2 ∣ n + k)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [truncatedProperPrimePowerCount_cast_eq_indicatorSum]
    _ = ∑ n ∈ sieveInterval K,
        ∑ pa ∈ I, ∑ qb ∈ I,
          Erdos248.sieveWeight K n *
            (Erdos248.realIndicator (pa.1 ^ pa.2 ∣ n + k) *
              Erdos248.realIndicator (qb.1 ^ qb.2 ∣ n + k)) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [pow_two, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
    _ = ∑ pa ∈ I, ∑ qb ∈ I,
        ∑ n ∈ sieveInterval K,
          Erdos248.sieveWeight K n *
            (Erdos248.realIndicator (pa.1 ^ pa.2 ∣ n + k) *
              Erdos248.realIndicator (qb.1 ^ qb.2 ∣ n + k)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro pa hpa
      rw [Finset.sum_comm]
    _ = ∑ pa ∈ properPrimePowerIndices J,
        ∑ qb ∈ properPrimePowerIndices J,
          primePowerPairEventMass K k pa.1 pa.2 qb.1 qb.2 := by
      dsimp [I]
      apply Finset.sum_congr rfl
      intro pa hpa
      apply Finset.sum_congr rfl
      intro qb hqb
      unfold primePowerPairEventMass BoundedGaps.Maynard.sieveWeightSum
        sieveInterval
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hp : pa.1 ^ pa.2 ∣ n + k <;>
        by_cases hq : qb.1 ^ qb.2 ∣ n + k <;>
          simp [hp, hq, Erdos248.realIndicator]

theorem properPrimePowerIndices_mono {J B : ℕ} (hJB : J ≤ B) :
    properPrimePowerIndices J ⊆ properPrimePowerIndices B := by
  intro pa hpa
  have h := mem_properPrimePowerIndices_iff.mp hpa
  exact mem_properPrimePowerIndices_iff.mpr
    ⟨h.1, h.2.1.trans hJB, h.2.2.1, h.2.2.2.1.trans hJB,
      h.2.2.2.2.1, h.2.2.2.2.2.trans hJB⟩

/-- The pointwise transformed event estimates sum to a second-moment bound
whose only shift-dependence is the reciprocal mass of prime divisors of the
shift. -/
theorem truncatedPrimePowerSecondMoment_le_shiftReciprocal
    {A : ℝ} (hA : UniformWirsing A)
    {K J k : ℕ} (hreg : Erdos248.NormalizationRegular A K)
    (hJB : J ≤ 3 * Erdos248.intervalStart K) :
    truncatedPrimePowerSecondMoment K J k ≤
      2048 * Erdos248.sieveMass K *
          ((64 * shiftPrimeReciprocalMass J k + 4) ^ 2 +
            (128 * shiftPrimeReciprocalMass J k + 256)) +
        256 * primePowerErrorScale K * (J : ℝ) ^ 4 := by
  let I := properPrimePowerIndices J
  let S := Erdos248.sieveMass K
  let E := primePowerErrorScale K
  let d := fun pa : ℕ × ℕ => tailPrimePowerDensity K k pa
  let e := fun pa qb : ℕ × ℕ => tailSamePrimePowerDensity K k pa qb
  have hsub : I ⊆ properPrimePowerIndices (3 * Erdos248.intervalStart K) :=
    properPrimePowerIndices_mono hJB
  have hpair : ∀ pa ∈ I, ∀ qb ∈ I,
      primePowerPairEventMass K k pa.1 pa.2 qb.1 qb.2 ≤
        2048 * S * (d pa * d qb + e pa qb) + 256 * E := by
    intro pa hpa qb hqb
    have hpaB := hsub hpa
    have hqbB := hsub hqb
    by_cases hpq : pa.1 = qb.1
    · have hraw := samePrimePowerPairEventMass_le_tailDensity
        (k := k) hA hreg hpaB hqbB hpq
      calc
        primePowerPairEventMass K k pa.1 pa.2 qb.1 qb.2 ≤
            2048 * S * e pa qb + 256 * E := by simpa [S, E, e] using hraw
        _ ≤ 2048 * S * (d pa * d qb + e pa qb) + 256 * E := by
          have hS0 := (Erdos248.sieveMass_pos hA hreg).le
          have hd0 := mul_nonneg (tailPrimePowerDensity_nonneg K k pa)
            (tailPrimePowerDensity_nonneg K k qb)
          have hcoef : 0 ≤ 2048 * S :=
            mul_nonneg (by norm_num) (by simpa [S] using hS0)
          have hadd : e pa qb ≤ d pa * d qb + e pa qb :=
            le_add_of_nonneg_left hd0
          have hmul := mul_le_mul_of_nonneg_left hadd hcoef
          simpa [add_comm] using add_le_add_right hmul (256 * E)
    · have hraw := distinctPrimePowerPairEventMass_le_tailDensity
        (k := k) hA hreg hpaB hqbB hpq
      calc
        primePowerPairEventMass K k pa.1 pa.2 qb.1 qb.2 ≤
            2048 * S * d pa * d qb + 256 * E := by simpa [S, E, d] using hraw
        _ ≤ 2048 * S * (d pa * d qb + e pa qb) + 256 * E := by
          have hS0 := (Erdos248.sieveMass_pos hA hreg).le
          have he0 := tailSamePrimePowerDensity_nonneg K k pa qb
          have hcoef : 0 ≤ 2048 * S :=
            mul_nonneg (by norm_num) (by simpa [S] using hS0)
          calc
            2048 * S * d pa * d qb + 256 * E =
                2048 * S * (d pa * d qb) + 256 * E := by ring
            _ ≤ 2048 * S * (d pa * d qb + e pa qb) + 256 * E := by
              have hadd : d pa * d qb ≤ d pa * d qb + e pa qb :=
                le_add_of_nonneg_right he0
              have hmul := mul_le_mul_of_nonneg_left hadd hcoef
              simpa [add_comm] using add_le_add_right hmul (256 * E)
  have hraw : truncatedPrimePowerSecondMoment K J k ≤
      ∑ pa ∈ I, ∑ qb ∈ I,
        (2048 * S * (d pa * d qb + e pa qb) + 256 * E) := by
    rw [truncatedPrimePowerSecondMoment_eq_doublePairEventMass]
    apply Finset.sum_le_sum
    intro pa hpa
    apply Finset.sum_le_sum
    intro qb hqb
    exact hpair pa hpa qb hqb
  have hsumd : (∑ pa ∈ I, d pa) ≤
      64 * shiftPrimeReciprocalMass J k + 4 := by
    simpa [I, d] using sum_tailPrimePowerDensity_le_shiftReciprocal J K k hreg.1
  have hsume : (∑ pa ∈ I, ∑ qb ∈ I, e pa qb) ≤
      128 * shiftPrimeReciprocalMass J k + 256 := by
    simpa [I, e] using sum_tailSamePrimePowerDensity_le_shiftReciprocal J K k hreg.1
  have hsumd0 : 0 ≤ ∑ pa ∈ I, d pa := by
    apply Finset.sum_nonneg
    intro pa hpa
    exact tailPrimePowerDensity_nonneg K k pa
  have hsumdBound : (∑ pa ∈ I, d pa) ^ 2 ≤
      (64 * shiftPrimeReciprocalMass J k + 4) ^ 2 := by
    have hR0 : 0 ≤ shiftPrimeReciprocalMass J k := by
      unfold shiftPrimeReciprocalMass
      apply Finset.sum_nonneg
      intro p hp
      positivity
    exact (sq_le_sq₀ hsumd0 (by nlinarith)).2 hsumd
  have hprodSum :
      (∑ pa ∈ I, ∑ qb ∈ I, 2048 * S * (d pa * d qb)) =
        2048 * S * (∑ pa ∈ I, d pa) ^ 2 := by
    calc
      (∑ pa ∈ I, ∑ qb ∈ I, 2048 * S * (d pa * d qb)) =
          ∑ pa ∈ I, 2048 * S * (∑ qb ∈ I, d pa * d qb) := by
        apply Finset.sum_congr rfl
        intro pa hpa
        rw [Finset.mul_sum]
      _ = 2048 * S * (∑ pa ∈ I, ∑ qb ∈ I, d pa * d qb) := by
        rw [Finset.mul_sum]
      _ = 2048 * S * ((∑ pa ∈ I, d pa) * (∑ qb ∈ I, d qb)) := by
        rw [Finset.sum_mul_sum]
      _ = 2048 * S * (∑ pa ∈ I, d pa) ^ 2 := by ring
  have hsameSum :
      (∑ pa ∈ I, ∑ qb ∈ I, 2048 * S * e pa qb) =
        2048 * S * (∑ pa ∈ I, ∑ qb ∈ I, e pa qb) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro pa hpa
    rw [Finset.mul_sum]
  have hmainSum :
      (∑ pa ∈ I, ∑ qb ∈ I,
        2048 * S * (d pa * d qb + e pa qb)) =
        2048 * S * ((∑ pa ∈ I, d pa) ^ 2 +
          ∑ pa ∈ I, ∑ qb ∈ I, e pa qb) := by
    calc
      (∑ pa ∈ I, ∑ qb ∈ I,
        2048 * S * (d pa * d qb + e pa qb)) =
          ∑ pa ∈ I,
            ((∑ qb ∈ I, 2048 * S * (d pa * d qb)) +
              ∑ qb ∈ I, 2048 * S * e pa qb) := by
        simp_rw [mul_add]
        apply Finset.sum_congr rfl
        intro pa hpa
        rw [Finset.sum_add_distrib]
      _ = (∑ pa ∈ I, ∑ qb ∈ I, 2048 * S * (d pa * d qb)) +
            ∑ pa ∈ I, ∑ qb ∈ I, 2048 * S * e pa qb := by
        rw [Finset.sum_add_distrib]
      _ = 2048 * S * ((∑ pa ∈ I, d pa) ^ 2 +
          ∑ pa ∈ I, ∑ qb ∈ I, e pa qb) := by
        rw [hprodSum, hsameSum]
        ring
  have herrorSum :
      (∑ pa ∈ I, ∑ qb ∈ I, 256 * E) =
        256 * E * (I.card : ℝ) ^ 2 := by
    simp
    push_cast
    ring
  have hcard : I.card ≤ J ^ 2 := by
    have hsubset : I ⊆ (Finset.Icc 2 J).product (Finset.Icc 2 J) := by
      intro pa hpa
      have h := mem_properPrimePowerIndices_iff.mp hpa
      exact Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr ⟨h.1, h.2.1⟩,
          Finset.mem_Icc.mpr ⟨h.2.2.1, h.2.2.2.1⟩⟩
    calc
      I.card ≤ ((Finset.Icc 2 J).product (Finset.Icc 2 J)).card :=
        Finset.card_le_card hsubset
      _ = (Finset.Icc 2 J).card * (Finset.Icc 2 J).card :=
        Finset.card_product _ _
      _ ≤ J * J := by
        have hc : (Finset.Icc 2 J).card ≤ J := by simp
        exact Nat.mul_le_mul hc hc
      _ = J ^ 2 := by ring
  have hcard4 : ((I.card : ℝ) ^ 2) ≤ (J : ℝ) ^ 4 := by
    have hnat : I.card ^ 2 ≤ (J ^ 2) ^ 2 :=
      Nat.pow_le_pow_left hcard 2
    have hnat' : I.card ^ 2 ≤ J ^ 4 := by
      simpa [← pow_mul] using hnat
    exact_mod_cast hnat'
  calc
    truncatedPrimePowerSecondMoment K J k ≤
        ∑ pa ∈ I, ∑ qb ∈ I,
          (2048 * S * (d pa * d qb + e pa qb) + 256 * E) := hraw
    _ = (∑ pa ∈ I, ∑ qb ∈ I,
          2048 * S * (d pa * d qb + e pa qb)) +
        ∑ pa ∈ I, ∑ qb ∈ I, 256 * E := by
      simp_rw [Finset.sum_add_distrib]
    _ = 2048 * S * ((∑ pa ∈ I, d pa) ^ 2 +
          ∑ pa ∈ I, ∑ qb ∈ I, e pa qb) +
        256 * E * (I.card : ℝ) ^ 2 := by rw [hmainSum, herrorSum]
    _ ≤ 2048 * S *
          ((64 * shiftPrimeReciprocalMass J k + 4) ^ 2 +
            (128 * shiftPrimeReciprocalMass J k + 256)) +
        256 * E * (J : ℝ) ^ 4 := by
      have hS0 := (Erdos248.sieveMass_pos hA hreg).le
      have hE0 := primePowerErrorScale_nonneg K
      gcongr
    _ = 2048 * Erdos248.sieveMass K *
          ((64 * shiftPrimeReciprocalMass J k + 4) ^ 2 +
            (128 * shiftPrimeReciprocalMass J k + 256)) +
        256 * primePowerErrorScale K * (J : ℝ) ^ 4 := rfl

/-- At the first sieve radius, the fourth-order interval error is absorbed
by the sieve mass, leaving a uniform quadratic divisor-mass majorant. -/
theorem truncatedPrimePowerSecondMoment_le_absorbed
    {A : ℝ} (hA : UniformWirsing A)
    {K k : ℕ} (hreg : Erdos248.NormalizationRegular A K) :
    truncatedPrimePowerSecondMoment K (Erdos248.shiftRadius K 1) k ≤
      10240001 * Erdos248.sieveMass K *
        (shiftPrimeReciprocalMass (Erdos248.shiftRadius K 1) k ^ 2 + 1) := by
  let J := Erdos248.shiftRadius K 1
  let R := shiftPrimeReciprocalMass J k
  let S := Erdos248.sieveMass K
  have hJone : 1 ≤ J := (Erdos248.one_lt_shiftRadius K 1).le
  have hJX : J ≤ Erdos248.intervalStart K := by
    calc
      J ≤ J ^ 100 := Nat.le_pow (by norm_num)
      _ = Erdos248.intervalStart K := Erdos248.largestRadius_pow_hundred hreg.1
  have hJB : J ≤ 3 * Erdos248.intervalStart K := by omega
  have hraw := truncatedPrimePowerSecondMoment_le_shiftReciprocal
    (k := k) hA hreg hJB
  have hR0 : 0 ≤ R := by
    dsimp [R]
    unfold shiftPrimeReciprocalMass
    apply Finset.sum_nonneg
    intro p hp
    positivity
  have hpoly : (64 * R + 4) ^ 2 + (128 * R + 256) ≤
      5000 * (R ^ 2 + 1) := by
    nlinarith [sq_nonneg (R - 1)]
  have hS0 : 0 ≤ S := by
    dsimp [S]
    exact (Erdos248.sieveMass_pos hA hreg).le
  have hmain : 2048 * S * ((64 * R + 4) ^ 2 + (128 * R + 256)) ≤
      10240000 * S * (R ^ 2 + 1) := by
    calc
      2048 * S * ((64 * R + 4) ^ 2 + (128 * R + 256)) ≤
          2048 * S * (5000 * (R ^ 2 + 1)) := by
        exact mul_le_mul_of_nonneg_left hpoly
          (mul_nonneg (by norm_num) hS0)
      _ = 10240000 * S * (R ^ 2 + 1) := by ring
  have herrStrong := Erdos248.accumulatedFourthIntervalError_lt_sieveMass
    hA hreg (show J ≤ Erdos248.shiftRadius K 1 by rfl)
  have herr : 256 * primePowerErrorScale K * (J : ℝ) ^ 4 ≤ S := by
    have hJE : 0 ≤ (J : ℝ) ^ 4 * primePowerErrorScale K :=
      mul_nonneg (by positivity) (primePowerErrorScale_nonneg K)
    unfold primePowerErrorScale at herrStrong ⊢
    dsimp [S]
    nlinarith
  have herr' : 256 * primePowerErrorScale K * (J : ℝ) ^ 4 ≤
      S * (R ^ 2 + 1) := by
    calc
      256 * primePowerErrorScale K * (J : ℝ) ^ 4 ≤ S := herr
      _ ≤ S * (R ^ 2 + 1) := by
        have hR : 1 ≤ R ^ 2 + 1 := by nlinarith [sq_nonneg R]
        nlinarith [mul_le_mul_of_nonneg_left hR hS0]
  calc
    truncatedPrimePowerSecondMoment K J k ≤
        2048 * S * ((64 * R + 4) ^ 2 + (128 * R + 256)) +
          256 * primePowerErrorScale K * (J : ℝ) ^ 4 := by
      simpa [J, R, S] using hraw
    _ ≤ 10240000 * S * (R ^ 2 + 1) + S * (R ^ 2 + 1) :=
      add_le_add hmain herr'
    _ = 10240001 * S * (R ^ 2 + 1) := by ring
    _ = 10240001 * Erdos248.sieveMass K *
        (shiftPrimeReciprocalMass (Erdos248.shiftRadius K 1) k ^ 2 + 1) := by
      rfl

/-- Reciprocal squares along multiples of `l` cost at most the full
reciprocal-square series after quotienting by `l`. -/
theorem sum_Icc_filter_dvd_inv_sq_le_two_div_sq
    (M l : ℕ) (hl : 0 < l) :
    (∑ k ∈ (Finset.Icc 1 M).filter (fun k => l ∣ k),
        (1 : ℝ) / (k : ℝ) ^ 2) ≤ 2 / (l : ℝ) ^ 2 := by
  let S := (Finset.Icc 1 M).filter (fun k => l ∣ k)
  let U := S.image (fun k => k / l)
  have hinj : Set.InjOn (fun k : ℕ => k / l) S := by
    intro a ha b hb hab
    have hadvd : l ∣ a := (Finset.mem_filter.mp ha).2
    have hbdvd : l ∣ b := (Finset.mem_filter.mp hb).2
    calc
      a = l * (a / l) := (Nat.mul_div_cancel' hadvd).symm
      _ = l * (b / l) := by simpa using congrArg (fun z => l * z) hab
      _ = b := Nat.mul_div_cancel' hbdvd
  have hUsub : U ⊆ Finset.Icc 1 M := by
    intro m hm
    rcases Finset.mem_image.mp hm with ⟨k, hk, rfl⟩
    have hk' := Finset.mem_filter.mp hk
    have hkrange := Finset.mem_Icc.mp hk'.1
    have hldvd := hk'.2
    have hlk : l ≤ k := Nat.le_of_dvd (by omega) hldvd
    exact Finset.mem_Icc.mpr
      ⟨Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.div_pos hlk hl)),
        (Nat.div_le_self k l).trans hkrange.2⟩
  have hreindex :
      (∑ k ∈ S, (1 : ℝ) / (k : ℝ) ^ 2) =
        ∑ m ∈ U, (1 : ℝ) / ((l * m : ℕ) : ℝ) ^ 2 := by
    dsimp [U]
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro k hk
    have hkdvd : l ∣ k := (Finset.mem_filter.mp hk).2
    rw [Nat.mul_div_cancel' hkdvd]
  calc
    (∑ k ∈ (Finset.Icc 1 M).filter (fun k => l ∣ k),
        (1 : ℝ) / (k : ℝ) ^ 2) =
        ∑ m ∈ U, (1 : ℝ) / ((l * m : ℕ) : ℝ) ^ 2 := by
      simpa [S] using hreindex
    _ ≤ ∑ m ∈ Finset.Icc 1 M,
        (1 : ℝ) / ((l * m : ℕ) : ℝ) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hUsub
      intro m hm hnot
      positivity
    _ = (1 : ℝ) / (l : ℝ) ^ 2 *
        ∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / (m : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      push_cast
      field_simp
    _ ≤ (1 : ℝ) / (l : ℝ) ^ 2 * 2 := by
      exact mul_le_mul_of_nonneg_left
        (Erdos248.sum_Icc_one_div_sq_le_two M) (by positivity)
    _ = 2 / (l : ℝ) ^ 2 := by ring

/-- The reciprocal divisor mass of a shift has a uniformly summable square
after division by the square of the shift. -/
theorem sum_shiftPrimeReciprocalMass_sq_div_sq_le_eight (B M : ℕ) :
    (∑ k ∈ Finset.Icc 1 M,
        shiftPrimeReciprocalMass B k ^ 2 / (k : ℝ) ^ 2) ≤ 8 := by
  let P := Finset.Icc 2 B
  let K := Finset.Icc 1 M
  have hsq (k : ℕ) :
      shiftPrimeReciprocalMass B k ^ 2 =
        ∑ p ∈ P, ∑ q ∈ P,
          if Nat.lcm p q ∣ k then
            ((1 : ℝ) / p) * ((1 : ℝ) / q) else 0 := by
    unfold shiftPrimeReciprocalMass
    dsimp [P]
    simp_rw [Finset.sum_filter]
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    by_cases hpdvd : p ∣ k <;> by_cases hqdvd : q ∣ k
    · have hlcm : Nat.lcm p q ∣ k := Nat.lcm_dvd hpdvd hqdvd
      simp [hpdvd, hqdvd, hlcm]
    · have hlcm : ¬ Nat.lcm p q ∣ k := by
        intro h
        exact hqdvd ((Nat.dvd_lcm_right p q).trans h)
      simp [hpdvd, hqdvd, hlcm]
    · have hlcm : ¬ Nat.lcm p q ∣ k := by
        intro h
        exact hpdvd ((Nat.dvd_lcm_left p q).trans h)
      simp [hpdvd, hqdvd, hlcm]
    · have hlcm : ¬ Nat.lcm p q ∣ k := by
        intro h
        exact hpdvd ((Nat.dvd_lcm_left p q).trans h)
      simp [hpdvd, hqdvd, hlcm]
  have hexpand :
      (∑ k ∈ K, shiftPrimeReciprocalMass B k ^ 2 / (k : ℝ) ^ 2) =
        ∑ p ∈ P, ∑ q ∈ P,
          ((1 : ℝ) / p) * ((1 : ℝ) / q) *
            (∑ k ∈ K.filter (fun k => Nat.lcm p q ∣ k),
              (1 : ℝ) / (k : ℝ) ^ 2) := by
    calc
      (∑ k ∈ K, shiftPrimeReciprocalMass B k ^ 2 / (k : ℝ) ^ 2) =
          ∑ k ∈ K, ∑ p ∈ P, ∑ q ∈ P,
            if Nat.lcm p q ∣ k then
              (((1 : ℝ) / p) * ((1 : ℝ) / q)) /
                (k : ℝ) ^ 2 else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hsq]
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro q hq
        split_ifs <;> simp
      _ = ∑ p ∈ P, ∑ q ∈ P, ∑ k ∈ K,
          if Nat.lcm p q ∣ k then
            (((1 : ℝ) / p) * ((1 : ℝ) / q)) /
              (k : ℝ) ^ 2 else 0 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.sum_comm]
      _ = ∑ p ∈ P, ∑ q ∈ P,
          ((1 : ℝ) / p) * ((1 : ℝ) / q) *
            (∑ k ∈ K.filter (fun k => Nat.lcm p q ∣ k),
              (1 : ℝ) / (k : ℝ) ^ 2) := by
        apply Finset.sum_congr rfl
        intro p hp
        apply Finset.sum_congr rfl
        intro q hq
        simp_rw [Finset.sum_filter]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        split_ifs <;> simp
        ring
  have hterm : ∀ p ∈ P, ∀ q ∈ P,
      ((1 : ℝ) / p) * ((1 : ℝ) / q) *
          (∑ k ∈ K.filter (fun k => Nat.lcm p q ∣ k),
            (1 : ℝ) / (k : ℝ) ^ 2) ≤
        2 / ((p : ℝ) ^ 2 * (q : ℝ) ^ 2) := by
    intro p hp q hq
    have hp2 := (Finset.mem_Icc.mp hp).1
    have hq2 := (Finset.mem_Icc.mp hq).1
    have hlpos : 0 < Nat.lcm p q := Nat.lcm_pos (by omega) (by omega)
    have hmultiple := sum_Icc_filter_dvd_inv_sq_le_two_div_sq M
      (Nat.lcm p q) hlpos
    have hcoeff0 : 0 ≤ ((1 : ℝ) / p) * ((1 : ℝ) / q) := by positivity
    calc
      ((1 : ℝ) / p) * ((1 : ℝ) / q) *
          (∑ k ∈ K.filter (fun k => Nat.lcm p q ∣ k),
            (1 : ℝ) / (k : ℝ) ^ 2) ≤
          ((1 : ℝ) / p) * ((1 : ℝ) / q) *
            (2 / (Nat.lcm p q : ℝ) ^ 2) := by
        exact mul_le_mul_of_nonneg_left (by simpa [K] using hmultiple) hcoeff0
      _ ≤ 2 / ((p : ℝ) ^ 2 * (q : ℝ) ^ 2) := by
        let l := Nat.lcm p q
        have hpl : p ≤ l := Nat.le_of_dvd hlpos (Nat.dvd_lcm_left p q)
        have hql : q ≤ l := Nat.le_of_dvd hlpos (Nat.dvd_lcm_right p q)
        have hprod : p * q ≤ l ^ 2 := by
          simpa [pow_two] using Nat.mul_le_mul hpl hql
        have hdenNat : (p * q) ^ 2 ≤ p * q * l ^ 2 := by
          have := Nat.mul_le_mul_left (p * q) hprod
          simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using this
        have hden : (((p * q) ^ 2 : ℕ) : ℝ) ≤
            ((p * q * l ^ 2 : ℕ) : ℝ) := by exact_mod_cast hdenNat
        calc
          ((1 : ℝ) / p) * ((1 : ℝ) / q) *
              (2 / (Nat.lcm p q : ℝ) ^ 2) =
              2 / (((p * q * l ^ 2 : ℕ) : ℝ)) := by
            dsimp [l]
            push_cast
            field_simp
          _ ≤ 2 / (((p * q) ^ 2 : ℕ) : ℝ) := by
            exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
          _ = 2 / ((p : ℝ) ^ 2 * (q : ℝ) ^ 2) := by
            push_cast
            field_simp
  have hPsum : (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2) ≤ 2 := by
    calc
      (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2) ≤
          ∑ p ∈ Finset.Icc 1 B, (1 : ℝ) / (p : ℝ) ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          exact Finset.mem_Icc.mpr
            ⟨(show 1 ≤ 2 by norm_num).trans (Finset.mem_Icc.mp hp).1,
              (Finset.mem_Icc.mp hp).2⟩
        · intro p hp hnot
          positivity
      _ ≤ 2 := Erdos248.sum_Icc_one_div_sq_le_two B
  calc
    (∑ k ∈ Finset.Icc 1 M,
        shiftPrimeReciprocalMass B k ^ 2 / (k : ℝ) ^ 2) =
        ∑ p ∈ P, ∑ q ∈ P,
          ((1 : ℝ) / p) * ((1 : ℝ) / q) *
            (∑ k ∈ K.filter (fun k => Nat.lcm p q ∣ k),
              (1 : ℝ) / (k : ℝ) ^ 2) := by simpa [K] using hexpand
    _ ≤ ∑ p ∈ P, ∑ q ∈ P,
        2 / ((p : ℝ) ^ 2 * (q : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro q hq
      exact hterm p hp q hq
    _ = 2 * (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2) ^ 2 := by
      rw [pow_two, Finset.sum_mul_sum]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ ≤ 2 * 2 ^ 2 := by
      have hP0 : 0 ≤ ∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2 := by positivity
      exact mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ hP0 (by norm_num)).2 hPsum) (by norm_num)
    _ = 8 := by norm_num

/-- Markov's inequality turns the absorbed second moment into a pointwise
reciprocal-square bad-mass estimate. -/
theorem weightedTruncatedPrimePowerBadMass_le_reciprocal
    {A : ℝ} (hA : UniformWirsing A)
    {K k : ℕ} (hreg : Erdos248.NormalizationRegular A K) (hk1 : 1 ≤ k) :
    weightedTruncatedPrimePowerBadMass K (Erdos248.shiftRadius K 1)
        1000000 k ≤
      (10240001 * Erdos248.sieveMass K / (1000000 : ℝ) ^ 2) *
        ((shiftPrimeReciprocalMass (Erdos248.shiftRadius K 1) k ^ 2 + 1) /
          (k : ℝ) ^ 2) := by
  have hmark := sq_mul_weightedTruncatedPrimePowerBadMass_le_secondMoment
    K (Erdos248.shiftRadius K 1) 1000000 k
  have hmoment := truncatedPrimePowerSecondMoment_le_absorbed hA hreg (k := k)
  have htk : (0 : ℝ) < (((1000000 * k : ℕ) : ℝ) ^ 2) := by
    have hkpos : 0 < 1000000 * k := by omega
    exact pow_pos (by exact_mod_cast hkpos) _
  have hdiv : weightedTruncatedPrimePowerBadMass K
      (Erdos248.shiftRadius K 1) 1000000 k ≤
      truncatedPrimePowerSecondMoment K (Erdos248.shiftRadius K 1) k /
        (((1000000 * k : ℕ) : ℝ) ^ 2) := by
    apply (le_div_iff₀ htk).2
    simpa [mul_comm] using hmark
  calc
    weightedTruncatedPrimePowerBadMass K (Erdos248.shiftRadius K 1)
        1000000 k ≤
        truncatedPrimePowerSecondMoment K (Erdos248.shiftRadius K 1) k /
          (((1000000 * k : ℕ) : ℝ) ^ 2) := hdiv
    _ ≤ (10240001 * Erdos248.sieveMass K *
          (shiftPrimeReciprocalMass (Erdos248.shiftRadius K 1) k ^ 2 + 1)) /
        (((1000000 * k : ℕ) : ℝ) ^ 2) :=
      div_le_div_of_nonneg_right hmoment htk.le
    _ = (10240001 * Erdos248.sieveMass K / (1000000 : ℝ) ^ 2) *
        ((shiftPrimeReciprocalMass (Erdos248.shiftRadius K 1) k ^ 2 + 1) /
          (k : ℝ) ^ 2) := by
      push_cast
      field_simp

/-- The fixed truncation threshold spends at most one eighth of the sieve
mass after summing over every relevant shift. -/
theorem sum_weightedTruncatedPrimePowerBadMass_le_eighth
    {A : ℝ} (hA : UniformWirsing A)
    {K : ℕ} (hreg : Erdos248.NormalizationRegular A K) :
    (∑ k ∈ Finset.Icc 1 (Erdos248.intervalExponent K),
      weightedTruncatedPrimePowerBadMass K (Erdos248.shiftRadius K 1)
        1000000 k) ≤ Erdos248.sieveMass K / 8 := by
  let J := Erdos248.shiftRadius K 1
  let M := Erdos248.intervalExponent K
  let S := Erdos248.sieveMass K
  let c : ℝ := 10240001 * S / (1000000 : ℝ) ^ 2
  have hpoint : ∀ k ∈ Finset.Icc 1 M,
      weightedTruncatedPrimePowerBadMass K J 1000000 k ≤
        c * ((shiftPrimeReciprocalMass J k ^ 2 + 1) / (k : ℝ) ^ 2) := by
    intro k hk
    simpa [J, M, S, c] using
      (weightedTruncatedPrimePowerBadMass_le_reciprocal hA hreg
        (Finset.mem_Icc.mp hk).1)
  have hsumR : (∑ k ∈ Finset.Icc 1 M,
      shiftPrimeReciprocalMass J k ^ 2 / (k : ℝ) ^ 2) ≤ 8 :=
    sum_shiftPrimeReciprocalMass_sq_div_sq_le_eight J M
  have hsumOne : (∑ k ∈ Finset.Icc 1 M,
      (1 : ℝ) / (k : ℝ) ^ 2) ≤ 2 :=
    Erdos248.sum_Icc_one_div_sq_le_two M
  have hsum : (∑ k ∈ Finset.Icc 1 M,
      (shiftPrimeReciprocalMass J k ^ 2 + 1) / (k : ℝ) ^ 2) ≤ 10 := by
    calc
      (∑ k ∈ Finset.Icc 1 M,
        (shiftPrimeReciprocalMass J k ^ 2 + 1) / (k : ℝ) ^ 2) =
          (∑ k ∈ Finset.Icc 1 M,
            shiftPrimeReciprocalMass J k ^ 2 / (k : ℝ) ^ 2) +
          ∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / (k : ℝ) ^ 2 := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ ≤ 8 + 2 := add_le_add hsumR hsumOne
      _ = 10 := by norm_num
  have hc0 : 0 ≤ c := by
    dsimp [c, S]
    exact div_nonneg
      (mul_nonneg (by norm_num) (Erdos248.sieveMass_pos hA hreg).le)
      (by positivity)
  have hnum : (10240001 : ℝ) * 10 / (1000000 : ℝ) ^ 2 ≤ 1 / 8 := by
    norm_num
  calc
    (∑ k ∈ Finset.Icc 1 (Erdos248.intervalExponent K),
      weightedTruncatedPrimePowerBadMass K (Erdos248.shiftRadius K 1)
        1000000 k) =
        ∑ k ∈ Finset.Icc 1 M,
          weightedTruncatedPrimePowerBadMass K J 1000000 k := by rfl
    _ ≤ ∑ k ∈ Finset.Icc 1 M,
        c * ((shiftPrimeReciprocalMass J k ^ 2 + 1) / (k : ℝ) ^ 2) :=
      Finset.sum_le_sum hpoint
    _ = c * ∑ k ∈ Finset.Icc 1 M,
        ((shiftPrimeReciprocalMass J k ^ 2 + 1) / (k : ℝ) ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ c * 10 := mul_le_mul_of_nonneg_left hsum hc0
    _ = S * ((10240001 : ℝ) * 10 / (1000000 : ℝ) ^ 2) := by
      dsimp [c]
      ring
    _ ≤ S * (1 / 8) := by
      exact mul_le_mul_of_nonneg_left hnum
        (by dsimp [S]; exact (Erdos248.sieveMass_pos hA hreg).le)
    _ = Erdos248.sieveMass K / 8 := by
      dsimp [S]
      ring

end TaoTeravainen
