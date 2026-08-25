import Util.TaoTeravainen.PrimePowerTail

noncomputable section

open scoped ArithmeticFunction.omega ArithmeticFunction.Omega BigOperators
open BoundedGaps.Maynard

namespace TaoTeravainen

local instance primePowerAbsorbedDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

abbrev UniformWirsing (A : ℝ) : Prop :=
  ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
    |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
        coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
      10 * coprimeHarmonicDensity (primorial D * P) *
        (A + Real.log D + primeLogDivisorMass P + Real.log 2)

theorem ninetySixPow_div_tiny_add_one_le_one {K : ℕ} (hK : 0 < K) :
    (96 : ℝ) ^ K / ((Erdos248.tinyCutoff K + 1 : ℕ) : ℝ) ≤ 1 := by
  have hsq : (1 : ℝ) ≤ (K : ℝ) ^ 2 := by
    have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
    nlinarith [sq_nonneg ((K : ℝ) - 1)]
  have hstrong := Erdos248.real_second_ninetySix_div_tiny_add_one_le_one hK
  have hden : (0 : ℝ) < ((Erdos248.tinyCutoff K + 1 : ℕ) : ℝ) := by
    positivity
  have hmul : (96 : ℝ) ^ K ≤ (K : ℝ) ^ 2 * 96 ^ K := by
    have := mul_le_mul_of_nonneg_right hsq (show 0 ≤ (96 : ℝ) ^ K by positivity)
    nlinarith
  calc
    (96 : ℝ) ^ K / ((Erdos248.tinyCutoff K + 1 : ℕ) : ℝ) ≤
        (K : ℝ) ^ 2 * 96 ^ K /
          ((Erdos248.tinyCutoff K + 1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right hmul hden.le
    _ ≤ 1 := hstrong

def tailPrimePowerDensity (K k : ℕ) (pa : ℕ × ℕ) : ℝ :=
  if pa.1 ≤ Erdos248.tinyCutoff K then
    if pa.1 ∣ k then (1 : ℝ) / (pa.1 : ℝ) ^ (pa.2 - 1) else 0
  else
    96 ^ K / (pa.1 : ℝ) ^ pa.2

def tailSamePrimePowerDensity (K k : ℕ) (pa qb : ℕ × ℕ) : ℝ :=
  if pa.1 = qb.1 then
    if pa.1 ≤ Erdos248.tinyCutoff K then
      if pa.1 ∣ k then
        (1 : ℝ) / (pa.1 : ℝ) ^ (max pa.2 qb.2 - 1) else 0
    else
      96 ^ K / (pa.1 : ℝ) ^ (max pa.2 qb.2)
  else 0

theorem tailPrimePowerDensity_nonneg (K k : ℕ) (pa : ℕ × ℕ) :
    0 ≤ tailPrimePowerDensity K k pa := by
  unfold tailPrimePowerDensity
  split_ifs <;> positivity

theorem tailSamePrimePowerDensity_nonneg
    (K k : ℕ) (pa qb : ℕ × ℕ) :
    0 ≤ tailSamePrimePowerDensity K k pa qb := by
  unfold tailSamePrimePowerDensity
  split_ifs <;> positivity

def shiftPrimeReciprocalMass (B k : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 2 B).filter (fun p => p ∣ k), (1 : ℝ) / p

theorem sum_smallActivePrimePowerDensity_le_shiftReciprocal
    (B K k : ℕ) :
    (∑ pa ∈ smallActivePrimePowerIndices B K k,
        (1 : ℝ) / (pa.1 : ℝ) ^ (pa.2 - 1)) ≤
      64 * shiftPrimeReciprocalMass B k := by
  let P := (Finset.Icc 2 B).filter fun p => p ∣ k
  let E := Finset.Icc 2 B
  have hsub : smallActivePrimePowerIndices B K k ⊆ P.product E := by
    intro pa hpa
    have hpa' := Finset.mem_filter.mp hpa
    have hdata := mem_properPrimePowerIndices_iff.mp hpa'.1
    exact Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_Icc.mpr ⟨hdata.1, hdata.2.1⟩, hpa'.2.2⟩,
        Finset.mem_Icc.mpr ⟨hdata.2.2.1, hdata.2.2.2.1⟩⟩
  calc
    (∑ pa ∈ smallActivePrimePowerIndices B K k,
        (1 : ℝ) / (pa.1 : ℝ) ^ (pa.2 - 1)) ≤
        ∑ pa ∈ P.product E,
          (1 : ℝ) / (pa.1 : ℝ) ^ (pa.2 - 1) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro pa hpa hnot
      positivity
    _ = ∑ p ∈ P, ∑ a ∈ E,
          (1 : ℝ) / (p : ℝ) ^ (a - 1) := by
      exact Finset.sum_product P E
        (fun pa : ℕ × ℕ => (1 : ℝ) / (pa.1 : ℝ) ^ (pa.2 - 1))
    _ ≤ ∑ p ∈ P, 64 / (p : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact sum_Icc_inv_prime_pow_sub_one_le_sixtyfour_div B p
        (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
    _ = 64 * shiftPrimeReciprocalMass B k := by
      unfold shiftPrimeReciprocalMass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring

theorem sum_smallActive_samePrimePowerDensity_le_shiftReciprocal
    (B K k : ℕ) :
    (∑ pa ∈ smallActivePrimePowerIndices B K k,
      ∑ qb ∈ smallActivePrimePowerIndices B K k,
        if pa.1 = qb.1 then
          (1 : ℝ) / (pa.1 : ℝ) ^ (max pa.2 qb.2 - 1) else 0) ≤
      128 * shiftPrimeReciprocalMass B k := by
  let P := (Finset.Icc 2 B).filter fun p => p ∣ k
  let E := Finset.Icc 2 B
  have hsub : smallActivePrimePowerIndices B K k ⊆ P.product E := by
    intro pa hpa
    have hpa' := Finset.mem_filter.mp hpa
    have hdata := mem_properPrimePowerIndices_iff.mp hpa'.1
    exact Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_Icc.mpr ⟨hdata.1, hdata.2.1⟩, hpa'.2.2⟩,
        Finset.mem_Icc.mpr ⟨hdata.2.2.1, hdata.2.2.2.1⟩⟩
  calc
    (∑ pa ∈ smallActivePrimePowerIndices B K k,
      ∑ qb ∈ smallActivePrimePowerIndices B K k,
        if pa.1 = qb.1 then
          (1 : ℝ) / (pa.1 : ℝ) ^ (max pa.2 qb.2 - 1) else 0) ≤
        ∑ p ∈ P, ∑ a ∈ E, ∑ b ∈ E,
          (1 : ℝ) / (p : ℝ) ^ (max a b - 1) := by
      apply sum_eq_base_pair_le_triple
        (smallActivePrimePowerIndices B K k) P E
        (fun p a b => (1 : ℝ) / (p : ℝ) ^ (max a b - 1)) hsub
      intro p hp a ha b hb
      positivity
    _ ≤ ∑ p ∈ P, 128 / (p : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact sum_Icc_pair_inv_pow_max_sub_one_le_onehundredtwentyeight_div B p
        (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
    _ = 128 * shiftPrimeReciprocalMass B k := by
      unfold shiftPrimeReciprocalMass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring

theorem sum_tailPrimePowerDensity_le_shiftReciprocal
    (B K k : ℕ) (hK : 0 < K) :
    (∑ pa ∈ properPrimePowerIndices B, tailPrimePowerDensity K k pa) ≤
      64 * shiftPrimeReciprocalMass B k + 4 := by
  have hsmall := sum_smallActivePrimePowerDensity_le_shiftReciprocal B K k
  have hlarge := sum_nonTinyPrimePowerDensity_le_div_tiny B K
  have h96 := ninetySixPow_div_tiny_add_one_le_one hK
  have hlarge' :
      96 ^ K * (∑ pa ∈ nonTinyPrimePowerIndices B K,
        (1 : ℝ) / (pa.1 : ℝ) ^ pa.2) ≤ 4 := by
    calc
      96 ^ K * (∑ pa ∈ nonTinyPrimePowerIndices B K,
          (1 : ℝ) / (pa.1 : ℝ) ^ pa.2) ≤
          96 ^ K * (4 / ((Erdos248.tinyCutoff K + 1 : ℕ) : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hlarge (by positivity)
      _ = 4 * (96 ^ K / ((Erdos248.tinyCutoff K + 1 : ℕ) : ℝ)) := by ring
      _ ≤ 4 := by nlinarith
  unfold tailPrimePowerDensity
  rw [Finset.sum_ite, Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero]
  simpa [smallActivePrimePowerIndices, nonTinyPrimePowerIndices,
    Finset.filter_filter, and_assoc, not_le, Finset.mul_sum, div_eq_mul_inv] using
    add_le_add hsmall hlarge'

theorem sum_tailSamePrimePowerDensity_le_shiftReciprocal
    (B K k : ℕ) (hK : 0 < K) :
    (∑ pa ∈ properPrimePowerIndices B,
      ∑ qb ∈ properPrimePowerIndices B,
        tailSamePrimePowerDensity K k pa qb) ≤
      128 * shiftPrimeReciprocalMass B k + 256 := by
  have hsmall := sum_smallActive_samePrimePowerDensity_le_shiftReciprocal B K k
  have hlarge := sum_nonTiny_samePrimePowerDensity_le_div_tiny B K
  have h96 := ninetySixPow_div_tiny_add_one_le_one hK
  have hlarge' :
      96 ^ K * (∑ pa ∈ nonTinyPrimePowerIndices B K,
        ∑ qb ∈ nonTinyPrimePowerIndices B K,
          if pa.1 = qb.1 then
            (1 : ℝ) / (pa.1 : ℝ) ^ (max pa.2 qb.2) else 0) ≤ 256 := by
    calc
      96 ^ K * (∑ pa ∈ nonTinyPrimePowerIndices B K,
        ∑ qb ∈ nonTinyPrimePowerIndices B K,
          if pa.1 = qb.1 then
            (1 : ℝ) / (pa.1 : ℝ) ^ (max pa.2 qb.2) else 0) ≤
          96 ^ K * (256 / ((Erdos248.tinyCutoff K + 1 : ℕ) : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hlarge (by positivity)
      _ = 256 * (96 ^ K /
          ((Erdos248.tinyCutoff K + 1 : ℕ) : ℝ)) := by ring
      _ ≤ 256 := by nlinarith
  have hdecomp :
      (∑ pa ∈ properPrimePowerIndices B,
        ∑ qb ∈ properPrimePowerIndices B,
          tailSamePrimePowerDensity K k pa qb) =
        (∑ pa ∈ smallActivePrimePowerIndices B K k,
          ∑ qb ∈ smallActivePrimePowerIndices B K k,
            if pa.1 = qb.1 then
              (1 : ℝ) / (pa.1 : ℝ) ^ (max pa.2 qb.2 - 1) else 0) +
        96 ^ K * (∑ pa ∈ nonTinyPrimePowerIndices B K,
          ∑ qb ∈ nonTinyPrimePowerIndices B K,
            if pa.1 = qb.1 then
              (1 : ℝ) / (pa.1 : ℝ) ^ (max pa.2 qb.2) else 0) := by
    unfold tailSamePrimePowerDensity
    unfold smallActivePrimePowerIndices nonTinyPrimePowerIndices
    simp only [Finset.sum_filter]
    rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro pa hpa
    by_cases hsmall : pa.1 ≤ Erdos248.tinyCutoff K
    · by_cases hdvd : pa.1 ∣ k
      · simp [smallActivePrimePowerIndices, nonTinyPrimePowerIndices,
          hsmall, hdvd, not_lt_of_ge hsmall, Finset.mul_sum,
          div_eq_mul_inv]
        apply Finset.sum_congr rfl
        intro qb hqb
        by_cases heq : pa.1 = qb.1
        · have hqsmall : qb.1 ≤ Erdos248.tinyCutoff K := heq ▸ hsmall
          have hqdvd : qb.1 ∣ k := heq ▸ hdvd
          simp [heq, hqsmall, hqdvd, div_eq_mul_inv]
        · simp [heq]
      · simp [smallActivePrimePowerIndices, nonTinyPrimePowerIndices,
          hsmall, hdvd, not_lt_of_ge hsmall, Finset.mul_sum,
          div_eq_mul_inv]
    · have hlarge : Erdos248.tinyCutoff K < pa.1 := by omega
      simp [smallActivePrimePowerIndices, nonTinyPrimePowerIndices,
        hsmall, hlarge, Finset.mul_sum, div_eq_mul_inv]
      apply Finset.sum_congr rfl
      intro qb hqb
      by_cases heq : pa.1 = qb.1
      · have hqlarge : Erdos248.tinyCutoff K < qb.1 := heq ▸ hlarge
        have hqnotSmall : ¬ qb.1 ≤ Erdos248.tinyCutoff K := by omega
        simp [heq, hsmall, hlarge, hqlarge, hqnotSmall,
          div_eq_mul_inv]
      · simp [heq]
  rw [hdecomp]
  exact add_le_add hsmall hlarge'

theorem scaled_productCoordinateEnergy_le_four_sieveMass
    {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K : ℕ} (hreg : Erdos248.NormalizationRegular A K) :
    (Erdos248.intervalStart K : ℝ) / Erdos248.preSieveModulus K *
        Erdos248.productCoordinateEnergy K ≤ 4 * Erdos248.sieveMass K := by
  have hquarter := Erdos248.quarter_scaled_energy_lt_sieveMass hA hreg
  have hident :
      (Erdos248.intervalStart K : ℝ) / Erdos248.preSieveModulus K *
          ((1 / 4 : ℝ) * Erdos248.productCoordinateEnergy K) =
        ((Erdos248.intervalStart K : ℝ) / Erdos248.preSieveModulus K *
          Erdos248.productCoordinateEnergy K) / 4 := by ring
  rw [hident] at hquarter
  nlinarith

theorem sharpPrimePowerEnergyBracket_le_five_quarters
    {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K : ℕ} (hreg : Erdos248.NormalizationRegular A K) :
    Erdos248.varyingYEnergy K (Erdos248.sieveY K) +
        roughCrossTupleTotientSquareTail (Erdos248.nearShifts K)
          (Erdos248.tinyCutoff K) (Erdos248.globalRadius K) *
          ∏ h : Erdos248.nearShifts K,
            Erdos248.varyingCoordinateMajorant K h ≤
      (5 / 4 : ℝ) * Erdos248.productCoordinateEnergy K := by
  have hY := Erdos248.varyingYEnergy_sieveY_le K
  have hprod := Erdos248.varyingMajorantProduct_le_energy hA hreg
  have htail := roughCross_mul_ninetySixPow_le_quarter hreg.1
  have hT0 : 0 ≤ roughCrossTupleTotientSquareTail (Erdos248.nearShifts K)
      (Erdos248.tinyCutoff K) (Erdos248.globalRadius K) := by
    unfold roughCrossTupleTotientSquareTail crossTotientSquareWeight
    positivity
  have hE0 := Erdos248.productCoordinateEnergy_nonneg K
  have hcross :
      roughCrossTupleTotientSquareTail (Erdos248.nearShifts K)
          (Erdos248.tinyCutoff K) (Erdos248.globalRadius K) *
          ∏ h : Erdos248.nearShifts K,
            Erdos248.varyingCoordinateMajorant K h ≤
        (1 / 4 : ℝ) * Erdos248.productCoordinateEnergy K := by
    calc
      roughCrossTupleTotientSquareTail (Erdos248.nearShifts K)
          (Erdos248.tinyCutoff K) (Erdos248.globalRadius K) *
          ∏ h : Erdos248.nearShifts K,
            Erdos248.varyingCoordinateMajorant K h ≤
          roughCrossTupleTotientSquareTail (Erdos248.nearShifts K)
            (Erdos248.tinyCutoff K) (Erdos248.globalRadius K) *
            (96 ^ K * Erdos248.productCoordinateEnergy K) := by
        exact mul_le_mul_of_nonneg_left hprod hT0
      _ = (roughCrossTupleTotientSquareTail (Erdos248.nearShifts K)
            (Erdos248.tinyCutoff K) (Erdos248.globalRadius K) * 96 ^ K) *
            Erdos248.productCoordinateEnergy K := by ring
      _ ≤ (1 / 4 : ℝ) * Erdos248.productCoordinateEnergy K := by
        exact mul_le_mul_of_nonneg_right htail hE0
  linarith

theorem primePowerMainScale_le_eight_ninetySixPow_sieveMass
    {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K : ℕ} (hreg : Erdos248.NormalizationRegular A K) :
    primePowerMainScale K ≤
      8 * 96 ^ K * Erdos248.sieveMass K := by
  have hscale := scaled_productCoordinateEnergy_le_four_sieveMass hA hreg
  have htail := roughCross_le_one hreg.1
  have hT0 : 0 ≤ roughCrossTupleTotientSquareTail (Erdos248.nearShifts K)
      (Erdos248.tinyCutoff K) (Erdos248.globalRadius K) := by
    unfold roughCrossTupleTotientSquareTail crossTotientSquareWeight
    positivity
  have hX0 : 0 ≤ (Erdos248.intervalStart K : ℝ) /
      Erdos248.preSieveModulus K := by positivity
  have hE0 := Erdos248.productCoordinateEnergy_nonneg K
  unfold primePowerMainScale primePowerEnergyBracket
  calc
    (Erdos248.intervalStart K : ℝ) / Erdos248.preSieveModulus K *
        ((1 + roughCrossTupleTotientSquareTail (Erdos248.nearShifts K)
          (Erdos248.tinyCutoff K) (Erdos248.globalRadius K)) *
          96 ^ K * Erdos248.productCoordinateEnergy K) ≤
        (Erdos248.intervalStart K : ℝ) / Erdos248.preSieveModulus K *
          (2 * 96 ^ K * Erdos248.productCoordinateEnergy K) := by
      apply mul_le_mul_of_nonneg_left _ hX0
      apply mul_le_mul_of_nonneg_right _ hE0
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = 2 * 96 ^ K *
          ((Erdos248.intervalStart K : ℝ) / Erdos248.preSieveModulus K *
            Erdos248.productCoordinateEnergy K) := by ring
    _ ≤ 2 * 96 ^ K * (4 * Erdos248.sieveMass K) := by
      exact mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = 8 * 96 ^ K * Erdos248.sieveMass K := by ring

theorem sharp_pair_scale_le_five_sieveMass
    {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K u v : ℕ} (hreg : Erdos248.NormalizationRegular A K)
    (hu : 0 < u) (hv : 0 < v) :
    (Erdos248.intervalStart K : ℝ) /
          (Erdos248.preSieveModulus K * u * v) *
        (Erdos248.varyingYEnergy K (Erdos248.sieveY K) +
          roughCrossTupleTotientSquareTail (Erdos248.nearShifts K)
            (Erdos248.tinyCutoff K) (Erdos248.globalRadius K) *
            ∏ h : Erdos248.nearShifts K,
              Erdos248.varyingCoordinateMajorant K h) ≤
      5 * Erdos248.sieveMass K * ((1 : ℝ) / u) * ((1 : ℝ) / v) := by
  have hbracket := sharpPrimePowerEnergyBracket_le_five_quarters hA hreg
  have hscale := scaled_productCoordinateEnergy_le_four_sieveMass hA hreg
  have hcoef : 0 ≤ (Erdos248.intervalStart K : ℝ) /
      (Erdos248.preSieveModulus K * u * v) := by positivity
  have hW : (Erdos248.preSieveModulus K : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Erdos248.preSieveModulus_pos K))
  have huR : (u : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hu)
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hv)
  calc
    (Erdos248.intervalStart K : ℝ) /
          (Erdos248.preSieveModulus K * u * v) *
        (Erdos248.varyingYEnergy K (Erdos248.sieveY K) +
          roughCrossTupleTotientSquareTail (Erdos248.nearShifts K)
            (Erdos248.tinyCutoff K) (Erdos248.globalRadius K) *
            ∏ h : Erdos248.nearShifts K,
              Erdos248.varyingCoordinateMajorant K h) ≤
        (Erdos248.intervalStart K : ℝ) /
          (Erdos248.preSieveModulus K * u * v) *
          ((5 / 4 : ℝ) * Erdos248.productCoordinateEnergy K) :=
      mul_le_mul_of_nonneg_left hbracket hcoef
    _ = (5 / 4 : ℝ) * ((1 : ℝ) / u) * ((1 : ℝ) / v) *
          ((Erdos248.intervalStart K : ℝ) / Erdos248.preSieveModulus K *
            Erdos248.productCoordinateEnergy K) := by
      push_cast
      field_simp
    _ ≤ (5 / 4 : ℝ) * ((1 : ℝ) / u) * ((1 : ℝ) / v) *
          (4 * Erdos248.sieveMass K) := by
      exact mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = 5 * Erdos248.sieveMass K * ((1 : ℝ) / u) * ((1 : ℝ) / v) := by
      ring

theorem sharp_single_scale_le_five_sieveMass
    {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K u : ℕ} (hreg : Erdos248.NormalizationRegular A K)
    (hu : 0 < u) :
    (Erdos248.intervalStart K : ℝ) /
          (Erdos248.preSieveModulus K * u) *
        (Erdos248.varyingYEnergy K (Erdos248.sieveY K) +
          roughCrossTupleTotientSquareTail (Erdos248.nearShifts K)
            (Erdos248.tinyCutoff K) (Erdos248.globalRadius K) *
            ∏ h : Erdos248.nearShifts K,
              Erdos248.varyingCoordinateMajorant K h) ≤
      5 * Erdos248.sieveMass K * ((1 : ℝ) / u) := by
  have hbracket := sharpPrimePowerEnergyBracket_le_five_quarters hA hreg
  have hscale := scaled_productCoordinateEnergy_le_four_sieveMass hA hreg
  have hcoef : 0 ≤ (Erdos248.intervalStart K : ℝ) /
      (Erdos248.preSieveModulus K * u) := by positivity
  have hW : (Erdos248.preSieveModulus K : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Erdos248.preSieveModulus_pos K))
  have huR : (u : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hu)
  calc
    (Erdos248.intervalStart K : ℝ) /
          (Erdos248.preSieveModulus K * u) *
        (Erdos248.varyingYEnergy K (Erdos248.sieveY K) +
          roughCrossTupleTotientSquareTail (Erdos248.nearShifts K)
            (Erdos248.tinyCutoff K) (Erdos248.globalRadius K) *
            ∏ h : Erdos248.nearShifts K,
              Erdos248.varyingCoordinateMajorant K h) ≤
        (Erdos248.intervalStart K : ℝ) /
          (Erdos248.preSieveModulus K * u) *
          ((5 / 4 : ℝ) * Erdos248.productCoordinateEnergy K) :=
      mul_le_mul_of_nonneg_left hbracket hcoef
    _ = (5 / 4 : ℝ) * ((1 : ℝ) / u) *
          ((Erdos248.intervalStart K : ℝ) / Erdos248.preSieveModulus K *
            Erdos248.productCoordinateEnergy K) := by
      push_cast
      field_simp
    _ ≤ (5 / 4 : ℝ) * ((1 : ℝ) / u) *
          (4 * Erdos248.sieveMass K) := by
      exact mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = 5 * Erdos248.sieveMass K * ((1 : ℝ) / u) := by ring

theorem coarse_pair_scale_le_tail
    {A : ℝ} {K : ℕ} (hA : UniformWirsing A)
    (hreg : Erdos248.NormalizationRegular A K)
    {d₁ d₂ t₁ t₂ : ℝ}
    (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂)
    (ht : 96 ^ K * d₁ * d₂ ≤ t₁ * t₂)
    (hmain : primePowerMainScale K ≤
      8 * 96 ^ K * Erdos248.sieveMass K) :
    256 * primePowerMainScale K * d₁ * d₂ ≤
      2048 * Erdos248.sieveMass K * t₁ * t₂ := by
  calc
    256 * primePowerMainScale K * d₁ * d₂ ≤
        256 * (8 * 96 ^ K * Erdos248.sieveMass K) * d₁ * d₂ := by
      gcongr
    _ = 2048 * Erdos248.sieveMass K * (96 ^ K * d₁ * d₂) := by ring
    _ ≤ 2048 * Erdos248.sieveMass K * (t₁ * t₂) := by
      exact mul_le_mul_of_nonneg_left ht
        (mul_nonneg (by norm_num) (Erdos248.sieveMass_pos hA hreg).le)
    _ = 2048 * Erdos248.sieveMass K * t₁ * t₂ := by ring

theorem coarse_single_scale_le_tail
    {A : ℝ} {K : ℕ} (hA : UniformWirsing A)
    (hreg : Erdos248.NormalizationRegular A K)
    {d t : ℝ} (hd : 0 ≤ d) (ht : 96 ^ K * d ≤ t)
    (hmain : primePowerMainScale K ≤
      8 * 96 ^ K * Erdos248.sieveMass K) :
    16 * primePowerMainScale K * d ≤
      128 * Erdos248.sieveMass K * t := by
  calc
    16 * primePowerMainScale K * d ≤
        16 * (8 * 96 ^ K * Erdos248.sieveMass K) * d := by
      gcongr
    _ = 128 * Erdos248.sieveMass K * (96 ^ K * d) := by ring
    _ ≤ 128 * Erdos248.sieveMass K * t := by
      exact mul_le_mul_of_nonneg_left ht
        (mul_nonneg (by norm_num) (Erdos248.sieveMass_pos hA hreg).le)

/-- Uniform distinct-base pair bound after absorbing the comparison factor. -/
theorem distinctPrimePowerPairEventMass_le_tailDensity
    {A : ℝ} (hA : UniformWirsing A)
    {K k : ℕ} (hreg : Erdos248.NormalizationRegular A K)
    {pa qb : ℕ × ℕ}
    (hpa : pa ∈ properPrimePowerIndices (3 * Erdos248.intervalStart K))
    (hqb : qb ∈ properPrimePowerIndices (3 * Erdos248.intervalStart K))
    (hpq : pa.1 ≠ qb.1) :
    primePowerPairEventMass K k pa.1 pa.2 qb.1 qb.2 ≤
      2048 * Erdos248.sieveMass K * tailPrimePowerDensity K k pa *
        tailPrimePowerDensity K k qb + 256 * primePowerErrorScale K := by
  have hpdata := mem_properPrimePowerIndices_iff.mp hpa
  have hqdata := mem_properPrimePowerIndices_iff.mp hqb
  have hp : pa.1.Prime := hpdata.2.2.2.2.1
  have hq : qb.1.Prime := hqdata.2.2.2.2.1
  have ha : 2 ≤ pa.2 := hpdata.2.2.1
  have hb : 2 ≤ qb.2 := hqdata.2.2.1
  have hpPos : 0 < pa.1 := hp.pos
  have hqPos : 0 < qb.1 := hq.pos
  have hmain := primePowerMainScale_le_eight_ninetySixPow_sieveMass hA hreg
  have hcoarse := distinctPrimePowerPairEventMass_le_density
    (k := k) hA hreg hpa hqb hpq
  have hE0 := primePowerErrorScale_nonneg K
  have hS0 := (Erdos248.sieveMass_pos hA hreg).le
  by_cases hpsmall : pa.1 ≤ Erdos248.tinyCutoff K
  · by_cases hpdiv : pa.1 ∣ k
    · by_cases hqsmall : qb.1 ≤ Erdos248.tinyCutoff K
      · by_cases hqdiv : qb.1 ∣ k
        · have hraw := smallDistinctPrimePowerPairEventMass_le_sharp
            (K := K) (k := k) hp hq hpq ha hb hpsmall hqsmall
          have hsharp := sharp_pair_scale_le_five_sieveMass hA hreg
            (u := pa.1 ^ (pa.2 - 1)) (v := qb.1 ^ (qb.2 - 1))
            (pow_pos hpPos _) (pow_pos hqPos _)
          calc
            primePowerPairEventMass K k pa.1 pa.2 qb.1 qb.2 ≤
                (Erdos248.intervalStart K : ℝ) /
                    (Erdos248.preSieveModulus K * pa.1 ^ (pa.2 - 1) *
                      qb.1 ^ (qb.2 - 1)) *
                  (Erdos248.varyingYEnergy K (Erdos248.sieveY K) +
                    roughCrossTupleTotientSquareTail (Erdos248.nearShifts K)
                      (Erdos248.tinyCutoff K) (Erdos248.globalRadius K) *
                      ∏ h : Erdos248.nearShifts K,
                        Erdos248.varyingCoordinateMajorant K h) +
                  primePowerErrorScale K := by
              simpa [primePowerErrorScale] using hraw
            _ ≤ 5 * Erdos248.sieveMass K *
                  ((1 : ℝ) / pa.1 ^ (pa.2 - 1)) *
                  ((1 : ℝ) / qb.1 ^ (qb.2 - 1)) +
                primePowerErrorScale K := by
              simpa [Nat.cast_pow, add_comm, add_left_comm, add_assoc] using
                (add_le_add_right hsharp (primePowerErrorScale K))
            _ ≤ 2048 * Erdos248.sieveMass K * tailPrimePowerDensity K k pa *
                  tailPrimePowerDensity K k qb + 256 * primePowerErrorScale K := by
              let x := Erdos248.sieveMass K *
                  ((1 : ℝ) / pa.1 ^ (pa.2 - 1)) *
                  ((1 : ℝ) / qb.1 ^ (qb.2 - 1))
              have hx : 0 ≤ x := by
                dsimp [x]
                exact mul_nonneg (mul_nonneg hS0 (by positivity)) (by positivity)
              have hscale : 5 * x + primePowerErrorScale K ≤
                  2048 * x + 256 * primePowerErrorScale K := by nlinarith
              simpa [tailPrimePowerDensity, hpsmall, hpdiv, hqsmall, hqdiv,
                x, one_div, mul_assoc] using hscale
        · rw [primePowerPairEventMass_comm K k pa.1 pa.2 qb.1 qb.2,
            smallPrimePowerPairEventMass_eq_zero_of_not_dvd hq hb hqsmall hqdiv]
          apply add_nonneg
          · exact mul_nonneg
              (mul_nonneg (mul_nonneg (by norm_num) hS0)
                (tailPrimePowerDensity_nonneg K k pa))
              (tailPrimePowerDensity_nonneg K k qb)
          · exact mul_nonneg (by norm_num) hE0
      · have hrel :
            96 ^ K * primePowerDensity K k pa * primePowerDensity K k qb ≤
              tailPrimePowerDensity K k pa * tailPrimePowerDensity K k qb := by
          simp [primePowerDensity, tailPrimePowerDensity, hpsmall, hpdiv,
            hqsmall, one_div, mul_assoc, mul_comm, mul_left_comm]
          rw [div_eq_mul_inv]
          ring_nf
          exact le_rfl
        have hscale := coarse_pair_scale_le_tail hA hreg
          (primePowerDensity_nonneg K k pa) (primePowerDensity_nonneg K k qb)
          hrel hmain
        exact hcoarse.trans (by
          simpa [add_comm, add_left_comm, add_assoc] using
            (add_le_add_right hscale (256 * primePowerErrorScale K)))
    · rw [smallPrimePowerPairEventMass_eq_zero_of_not_dvd hp ha hpsmall hpdiv]
      apply add_nonneg
      · exact mul_nonneg
          (mul_nonneg (mul_nonneg (by norm_num) hS0)
            (tailPrimePowerDensity_nonneg K k pa))
          (tailPrimePowerDensity_nonneg K k qb)
      · exact mul_nonneg (by norm_num) hE0
  · by_cases hqsmall : qb.1 ≤ Erdos248.tinyCutoff K
    · by_cases hqdiv : qb.1 ∣ k
      · have hrel :
            96 ^ K * primePowerDensity K k pa * primePowerDensity K k qb ≤
              tailPrimePowerDensity K k pa * tailPrimePowerDensity K k qb := by
          simp [primePowerDensity, tailPrimePowerDensity, hpsmall, hqsmall,
            hqdiv, one_div, mul_assoc, mul_comm, mul_left_comm]
          rw [div_eq_mul_inv]
          ring_nf
          exact le_rfl
        have hscale := coarse_pair_scale_le_tail hA hreg
          (primePowerDensity_nonneg K k pa) (primePowerDensity_nonneg K k qb)
          hrel hmain
        exact hcoarse.trans (by
          simpa [add_comm, add_left_comm, add_assoc] using
            (add_le_add_right hscale (256 * primePowerErrorScale K)))
      · rw [primePowerPairEventMass_comm K k pa.1 pa.2 qb.1 qb.2,
          smallPrimePowerPairEventMass_eq_zero_of_not_dvd hq hb hqsmall hqdiv]
        apply add_nonneg
        · exact mul_nonneg
            (mul_nonneg (mul_nonneg (by norm_num) hS0)
              (tailPrimePowerDensity_nonneg K k pa))
            (tailPrimePowerDensity_nonneg K k qb)
        · exact mul_nonneg (by norm_num) hE0
    · have h96one : (1 : ℝ) ≤ 96 ^ K := one_le_pow₀ (by norm_num)
      have hrel :
          96 ^ K * primePowerDensity K k pa * primePowerDensity K k qb ≤
            tailPrimePowerDensity K k pa * tailPrimePowerDensity K k qb := by
        simp [primePowerDensity, tailPrimePowerDensity, hpsmall, hqsmall,
          one_div]
        have hx : 0 ≤ ((pa.1 : ℝ) ^ pa.2)⁻¹ *
            (((qb.1 : ℝ) ^ qb.2)⁻¹) := by positivity
        calc
          96 ^ K * ((pa.1 : ℝ) ^ pa.2)⁻¹ *
              ((qb.1 : ℝ) ^ qb.2)⁻¹ =
              (96 ^ K) * (((pa.1 : ℝ) ^ pa.2)⁻¹ *
                ((qb.1 : ℝ) ^ qb.2)⁻¹) := by ring
          _ ≤ (96 ^ K * 96 ^ K) *
                (((pa.1 : ℝ) ^ pa.2)⁻¹ *
                  ((qb.1 : ℝ) ^ qb.2)⁻¹) := by
            apply mul_le_mul_of_nonneg_right _ hx
            simpa using (mul_le_mul_of_nonneg_left h96one
              (show 0 ≤ (96 : ℝ) ^ K by positivity))
          _ = (96 ^ K * ((pa.1 : ℝ) ^ pa.2)⁻¹) *
                (96 ^ K * ((qb.1 : ℝ) ^ qb.2)⁻¹) := by ring
      have hscale := coarse_pair_scale_le_tail hA hreg
        (primePowerDensity_nonneg K k pa) (primePowerDensity_nonneg K k qb)
        hrel hmain
      exact hcoarse.trans (by
        simpa [add_comm, add_left_comm, add_assoc] using
          (add_le_add_right hscale (256 * primePowerErrorScale K)))

/-- Uniform same-base pair bound after absorbing the comparison factor. -/
theorem samePrimePowerPairEventMass_le_tailDensity
    {A : ℝ} (hA : UniformWirsing A)
    {K k : ℕ} (hreg : Erdos248.NormalizationRegular A K)
    {pa qb : ℕ × ℕ}
    (hpa : pa ∈ properPrimePowerIndices (3 * Erdos248.intervalStart K))
    (hqb : qb ∈ properPrimePowerIndices (3 * Erdos248.intervalStart K))
    (hpq : pa.1 = qb.1) :
    primePowerPairEventMass K k pa.1 pa.2 qb.1 qb.2 ≤
      2048 * Erdos248.sieveMass K *
        tailSamePrimePowerDensity K k pa qb +
        256 * primePowerErrorScale K := by
  have hpdata := mem_properPrimePowerIndices_iff.mp hpa
  have hp : pa.1.Prime := hpdata.2.2.2.2.1
  have ha : 2 ≤ pa.2 := hpdata.2.2.1
  have hb : 2 ≤ qb.2 := (mem_properPrimePowerIndices_iff.mp hqb).2.2.1
  have hmax : 2 ≤ max pa.2 qb.2 := ha.trans (le_max_left _ _)
  have hpPos : 0 < pa.1 := hp.pos
  have hmain := primePowerMainScale_le_eight_ninetySixPow_sieveMass hA hreg
  have hcoarse := samePrimePowerPairEventMass_le_density
    (k := k) hA hreg hpa hqb hpq
  have hE0 := primePowerErrorScale_nonneg K
  have hS0 := (Erdos248.sieveMass_pos hA hreg).le
  by_cases hpsmall : pa.1 ≤ Erdos248.tinyCutoff K
  · by_cases hpdiv : pa.1 ∣ k
    · have hraw := smallPrimePowerEventMass_le_sharp
          (K := K) (k := k) hp hmax hpsmall
      have hsharp := sharp_single_scale_le_five_sieveMass hA hreg
        (u := pa.1 ^ (max pa.2 qb.2 - 1)) (pow_pos hpPos _)
      rw [show qb.1 = pa.1 by exact hpq.symm,
        primePowerPairEventMass_same_eq_max]
      calc
        primePowerEventMass K k pa.1 (max pa.2 qb.2) ≤
            (Erdos248.intervalStart K : ℝ) /
                (Erdos248.preSieveModulus K *
                  pa.1 ^ (max pa.2 qb.2 - 1)) *
              (Erdos248.varyingYEnergy K (Erdos248.sieveY K) +
                roughCrossTupleTotientSquareTail (Erdos248.nearShifts K)
                  (Erdos248.tinyCutoff K) (Erdos248.globalRadius K) *
                  ∏ h : Erdos248.nearShifts K,
                    Erdos248.varyingCoordinateMajorant K h) +
              primePowerErrorScale K := by
          simpa [primePowerErrorScale] using hraw
        _ ≤ 5 * Erdos248.sieveMass K *
              ((1 : ℝ) / pa.1 ^ (max pa.2 qb.2 - 1)) +
            primePowerErrorScale K := by
          simpa [Nat.cast_pow, add_comm, add_left_comm, add_assoc] using
            (add_le_add_right hsharp (primePowerErrorScale K))
        _ ≤ 2048 * Erdos248.sieveMass K *
              tailSamePrimePowerDensity K k pa qb +
            256 * primePowerErrorScale K := by
          have hqsmall : qb.1 ≤ Erdos248.tinyCutoff K := hpq ▸ hpsmall
          have hqdiv : qb.1 ∣ k := hpq ▸ hpdiv
          let x := Erdos248.sieveMass K *
              ((1 : ℝ) / pa.1 ^ (max pa.2 qb.2 - 1))
          have hx : 0 ≤ x := by
            dsimp [x]
            exact mul_nonneg hS0 (by positivity)
          have hscale : 5 * x + primePowerErrorScale K ≤
              2048 * x + 256 * primePowerErrorScale K := by nlinarith
          simpa [tailSamePrimePowerDensity, hpq, hpsmall, hpdiv, hqsmall,
            hqdiv, x, one_div, mul_assoc] using hscale
    · rw [show qb.1 = pa.1 by exact hpq.symm,
          primePowerPairEventMass_same_eq_max,
          smallPrimePowerEventMass_eq_zero_of_not_dvd hp hmax hpsmall hpdiv]
      apply add_nonneg
      · exact mul_nonneg
          (mul_nonneg (by norm_num) hS0)
          (tailSamePrimePowerDensity_nonneg K k pa qb)
      · exact mul_nonneg (by norm_num) hE0
  · have hrel :
        96 ^ K * samePrimePowerDensity K k pa qb ≤
          tailSamePrimePowerDensity K k pa qb := by
      have hqnotSmall : ¬ qb.1 ≤ Erdos248.tinyCutoff K := by
        rw [← hpq]
        exact hpsmall
      simp [samePrimePowerDensity, tailSamePrimePowerDensity, hpq,
        hpsmall, hqnotSmall, one_div, mul_assoc, mul_comm, mul_left_comm]
      rw [div_eq_mul_inv]
      ring_nf
      exact le_rfl
    have hscale := coarse_single_scale_le_tail hA hreg
      (samePrimePowerDensity_nonneg K k pa qb) hrel hmain
    calc
      primePowerPairEventMass K k pa.1 pa.2 qb.1 qb.2 ≤
          16 * primePowerMainScale K * samePrimePowerDensity K k pa qb +
            16 * primePowerErrorScale K := hcoarse
      _ ≤ 128 * Erdos248.sieveMass K *
            tailSamePrimePowerDensity K k pa qb +
          16 * primePowerErrorScale K :=
        by
          simpa [add_comm, add_left_comm, add_assoc] using
            (add_le_add_right hscale (16 * primePowerErrorScale K))
      _ ≤ 2048 * Erdos248.sieveMass K *
            tailSamePrimePowerDensity K k pa qb +
          256 * primePowerErrorScale K := by
        have hx : 0 ≤ Erdos248.sieveMass K *
            tailSamePrimePowerDensity K k pa qb :=
          mul_nonneg hS0 (tailSamePrimePowerDensity_nonneg K k pa qb)
        nlinarith

end TaoTeravainen
