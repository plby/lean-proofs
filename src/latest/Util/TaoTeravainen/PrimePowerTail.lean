import Util.TaoTeravainen.PrimePowerMoment
import Util.TaoTeravainen.PrimePowerSeries
import ErdosProblems.Erdos248.MediumScaleAbsorption

/-!
# Tao--Teräväinen: uniform prime-power moment tail

This module combines the exact prime-power event transforms with the finite
geometric budgets.  The first layer only normalizes all event bounds to one
common main scale and one interval-error scale.
-/

noncomputable section

open scoped ArithmeticFunction.omega ArithmeticFunction.Omega BigOperators
open BoundedGaps.Maynard

namespace TaoTeravainen

local instance primePowerTailDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- The common energy bracket appearing in every transformed event mass. -/
def primePowerEnergyBracket (K : ℕ) : ℝ :=
  (1 + BoundedGaps.Maynard.roughCrossTupleTotientSquareTail
      (Erdos248.nearShifts K) (Erdos248.tinyCutoff K)
      (Erdos248.globalRadius K)) *
    96 ^ K * Erdos248.productCoordinateEnergy K

/-- Common main scale before the prime-power density factors are inserted. -/
def primePowerMainScale (K : ℕ) : ℝ :=
  (Erdos248.intervalStart K : ℝ) / Erdos248.preSieveModulus K *
    primePowerEnergyBracket K

/-- Common absolute interval-error floor. -/
def primePowerErrorScale (K : ℕ) : ℝ :=
  (Erdos248.radiusProduct K : ℝ) ^ 6

theorem primePowerEnergyBracket_nonneg (K : ℕ) :
    0 ≤ primePowerEnergyBracket K := by
  unfold primePowerEnergyBracket
  have htail : 0 ≤ BoundedGaps.Maynard.roughCrossTupleTotientSquareTail
      (Erdos248.nearShifts K) (Erdos248.tinyCutoff K)
      (Erdos248.globalRadius K) := by
    unfold BoundedGaps.Maynard.roughCrossTupleTotientSquareTail
      BoundedGaps.Maynard.crossTotientSquareWeight
    positivity
  apply mul_nonneg
  · apply mul_nonneg
    · linarith
    · positivity
  · exact Erdos248.productCoordinateEnergy_nonneg K

theorem primePowerMainScale_nonneg (K : ℕ) :
    0 ≤ primePowerMainScale K := by
  unfold primePowerMainScale
  exact mul_nonneg (by positivity) (primePowerEnergyBracket_nonneg K)

theorem primePowerErrorScale_nonneg (K : ℕ) :
    0 ≤ primePowerErrorScale K := by
  unfold primePowerErrorScale
  positivity

/-- At the chosen scales, even the coarse varying-coordinate comparison is
absorbed by the pre-sieve cutoff once it is attached to the genuine cross
tail. -/
theorem roughCross_mul_ninetySixPow_le_quarter {K : ℕ} (hK : 0 < K) :
    roughCrossTupleTotientSquareTail (Erdos248.nearShifts K)
        (Erdos248.tinyCutoff K) (Erdos248.globalRadius K) * 96 ^ K ≤
      (1 / 4 : ℝ) := by
  let T := roughCrossTupleTotientSquareTail (Erdos248.nearShifts K)
    (Erdos248.tinyCutoff K) (Erdos248.globalRadius K)
  have htail := Erdos248.roughCrossTail_le_explicit hK
  have hD : (0 : ℝ) < Erdos248.tinyCutoff K := by
    exact_mod_cast Erdos248.tinyCutoff_pos K
  have hexp : Real.exp 8 ≤ (2 : ℝ) ^ 13 := Erdos248.exp_eight_le_two_pow_thirteen
  have hnat :
      3 * 2 ^ 18 * K ^ 2 * 96 ^ K ≤ Erdos248.tinyCutoff K :=
    Erdos248.cross_numeric_numerator_le_tinyCutoff hK
  calc
    T * 96 ^ K ≤
        (3 * (8 * Real.exp 8 / (Erdos248.tinyCutoff K : ℝ)) * K ^ 2) *
          96 ^ K := by
      exact mul_le_mul_of_nonneg_right (by simpa [T] using htail) (by positivity)
    _ ≤ (3 * (8 * (2 : ℝ) ^ 13 /
          (Erdos248.tinyCutoff K : ℝ)) * K ^ 2) * 96 ^ K := by
      gcongr
    _ = ((3 * 2 ^ 16 * K ^ 2 * 96 ^ K : ℕ) : ℝ) /
          Erdos248.tinyCutoff K := by
      push_cast
      norm_num
      ring
    _ ≤ (1 / 4 : ℝ) := by
      apply (div_le_iff₀ hD).2
      have hsmall :
          (((3 * 2 ^ 16 * K ^ 2 * 96 ^ K : ℕ) : ℝ)) * 4 ≤
            Erdos248.tinyCutoff K := by
        have hfour :
            (3 * 2 ^ 16 * K ^ 2 * 96 ^ K) * 4 =
              3 * 2 ^ 18 * K ^ 2 * 96 ^ K := by ring
        have hsmallNat :
            (3 * 2 ^ 16 * K ^ 2 * 96 ^ K) * 4 ≤
              Erdos248.tinyCutoff K := by
          rw [hfour]
          exact hnat
        exact_mod_cast hsmallNat
      calc
        ((3 * 2 ^ 16 * K ^ 2 * 96 ^ K : ℕ) : ℝ) ≤
            (Erdos248.tinyCutoff K : ℝ) / 4 := by
          exact (le_div_iff₀ (by norm_num)).2 hsmall
        _ = (1 / 4 : ℝ) * Erdos248.tinyCutoff K := by ring

theorem roughCross_le_one {K : ℕ} (hK : 0 < K) :
    roughCrossTupleTotientSquareTail (Erdos248.nearShifts K)
        (Erdos248.tinyCutoff K) (Erdos248.globalRadius K) ≤ 1 := by
  have h96 : (1 : ℝ) ≤ 96 ^ K := by
    exact one_le_pow₀ (by norm_num)
  have hT0 : 0 ≤ roughCrossTupleTotientSquareTail (Erdos248.nearShifts K)
      (Erdos248.tinyCutoff K) (Erdos248.globalRadius K) := by
    unfold roughCrossTupleTotientSquareTail crossTotientSquareWeight
    positivity
  have hmul := roughCross_mul_ninetySixPow_le_quarter hK
  nlinarith [mul_le_mul_of_nonneg_left h96 hT0]

/-- Algebraic normalization of a two-prime-power transformed mass bound. -/
theorem pair_event_scale_identity (K u v : ℕ) (C : ℝ)
    (hu : 0 < u) (hv : 0 < v) :
    (Erdos248.intervalStart K : ℝ) /
          ((Erdos248.preSieveModulus K * u) * v) *
        (C * primePowerEnergyBracket K) +
        primePowerErrorScale K * C =
      C * primePowerMainScale K * ((1 : ℝ) / u) * ((1 : ℝ) / v) +
        C * primePowerErrorScale K := by
  unfold primePowerMainScale
  have hW : (Erdos248.preSieveModulus K : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Erdos248.preSieveModulus_pos K))
  have huR : (u : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hu)
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hv)
  push_cast
  field_simp

/-- Algebraic normalization of a same-base transformed mass bound. -/
theorem single_event_scale_identity (K u : ℕ) (C : ℝ)
    (hu : 0 < u) :
    (Erdos248.intervalStart K : ℝ) /
          (Erdos248.preSieveModulus K * u) *
        (C * primePowerEnergyBracket K) +
        primePowerErrorScale K * C =
      C * primePowerMainScale K * ((1 : ℝ) / u) +
        C * primePowerErrorScale K := by
  unfold primePowerMainScale
  have hW : (Erdos248.preSieveModulus K : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Erdos248.preSieveModulus_pos K))
  have huR : (u : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hu)
  push_cast
  field_simp

theorem primePowerDensity_nonneg (K k : ℕ) (pa : ℕ × ℕ) :
    0 ≤ primePowerDensity K k pa := by
  unfold primePowerDensity
  split_ifs <;> positivity

theorem samePrimePowerDensity_nonneg (K k : ℕ) (pa qb : ℕ × ℕ) :
    0 ≤ samePrimePowerDensity K k pa qb := by
  unfold samePrimePowerDensity
  split_ifs <;> positivity

theorem scaled_pair_density_nonneg (K k : ℕ) (pa qb : ℕ × ℕ) :
    0 ≤ 256 * primePowerMainScale K * primePowerDensity K k pa *
        primePowerDensity K k qb + 256 * primePowerErrorScale K := by
  apply add_nonneg
  · exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (primePowerMainScale_nonneg K))
        (primePowerDensity_nonneg K k pa))
      (primePowerDensity_nonneg K k qb)
  · exact mul_nonneg (by norm_num) (primePowerErrorScale_nonneg K)

/-- Every distinct-base prime-power pair is bounded by the product of the
one-prime densities, with one fixed transform constant. -/
theorem distinctPrimePowerPairEventMass_le_density
    {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K k : ℕ} (hreg : Erdos248.NormalizationRegular A K)
    {pa qb : ℕ × ℕ}
    (hpa : pa ∈ properPrimePowerIndices (3 * Erdos248.intervalStart K))
    (hqb : qb ∈ properPrimePowerIndices (3 * Erdos248.intervalStart K))
    (hpq : pa.1 ≠ qb.1) :
    primePowerPairEventMass K k pa.1 pa.2 qb.1 qb.2 ≤
      256 * primePowerMainScale K * primePowerDensity K k pa *
        primePowerDensity K k qb + 256 * primePowerErrorScale K := by
  have hpdata := mem_properPrimePowerIndices_iff.mp hpa
  have hqdata := mem_properPrimePowerIndices_iff.mp hqb
  have hp : pa.1.Prime := hpdata.2.2.2.2.1
  have hq : qb.1.Prime := hqdata.2.2.2.2.1
  have ha : 2 ≤ pa.2 := hpdata.2.2.1
  have hb : 2 ≤ qb.2 := hqdata.2.2.1
  have hpPos : 0 < pa.1 := hp.pos
  have hqPos : 0 < qb.1 := hq.pos
  by_cases hpsmall : pa.1 ≤ Erdos248.tinyCutoff K
  · by_cases hpdiv : pa.1 ∣ k
    · by_cases hqsmall : qb.1 ≤ Erdos248.tinyCutoff K
      · by_cases hqdiv : qb.1 ∣ k
        · have hraw := smallDistinctPrimePowerPairEventMass_le_productCoordinateEnergy
            (K := K) (k := k) hA hreg hp hq hpq ha hb hpsmall hqsmall
          have hnorm :
              (Erdos248.intervalStart K : ℝ) /
                  (Erdos248.preSieveModulus K * pa.1 ^ (pa.2 - 1) *
                    qb.1 ^ (qb.2 - 1)) *
                ((1 + BoundedGaps.Maynard.roughCrossTupleTotientSquareTail
                    (Erdos248.nearShifts K) (Erdos248.tinyCutoff K)
                    (Erdos248.globalRadius K)) *
                  96 ^ K * Erdos248.productCoordinateEnergy K) +
                (Erdos248.radiusProduct K : ℝ) ^ 6 =
              primePowerMainScale K *
                  ((1 : ℝ) / pa.1 ^ (pa.2 - 1)) *
                  ((1 : ℝ) / qb.1 ^ (qb.2 - 1)) +
                primePowerErrorScale K := by
            simpa [primePowerEnergyBracket, primePowerErrorScale, mul_assoc] using
              (pair_event_scale_identity K (pa.1 ^ (pa.2 - 1))
                (qb.1 ^ (qb.2 - 1)) 1 (pow_pos hpPos _) (pow_pos hqPos _))
          calc
            primePowerPairEventMass K k pa.1 pa.2 qb.1 qb.2 ≤
                (Erdos248.intervalStart K : ℝ) /
                    (Erdos248.preSieveModulus K * pa.1 ^ (pa.2 - 1) *
                      qb.1 ^ (qb.2 - 1)) *
                  ((1 + BoundedGaps.Maynard.roughCrossTupleTotientSquareTail
                      (Erdos248.nearShifts K) (Erdos248.tinyCutoff K)
                      (Erdos248.globalRadius K)) *
                    96 ^ K * Erdos248.productCoordinateEnergy K) +
                  (Erdos248.radiusProduct K : ℝ) ^ 6 := hraw
            _ = primePowerMainScale K *
                  ((1 : ℝ) / pa.1 ^ (pa.2 - 1)) *
                  ((1 : ℝ) / qb.1 ^ (qb.2 - 1)) +
                primePowerErrorScale K := hnorm
            _ ≤ 256 * primePowerMainScale K * primePowerDensity K k pa *
                  primePowerDensity K k qb + 256 * primePowerErrorScale K := by
              simp only [one_div]
              have hm := primePowerMainScale_nonneg K
              have he := primePowerErrorScale_nonneg K
              have hd1 : 0 ≤ (1 : ℝ) / pa.1 ^ (pa.2 - 1) := by positivity
              have hd2 : 0 ≤ (1 : ℝ) / qb.1 ^ (qb.2 - 1) := by positivity
              have hx : 0 ≤ primePowerMainScale K *
                  ((1 : ℝ) / pa.1 ^ (pa.2 - 1)) *
                  ((1 : ℝ) / qb.1 ^ (qb.2 - 1)) :=
                mul_nonneg (mul_nonneg hm hd1) hd2
              let x := primePowerMainScale K *
                ((1 : ℝ) / pa.1 ^ (pa.2 - 1)) *
                ((1 : ℝ) / qb.1 ^ (qb.2 - 1))
              have hx' : 0 ≤ x := by simpa [x] using hx
              have hscale : x + primePowerErrorScale K ≤
                  256 * x + 256 * primePowerErrorScale K := by nlinarith
              simpa [x, one_div, mul_assoc] using hscale
        · rw [primePowerPairEventMass_comm K k pa.1 pa.2 qb.1 qb.2,
            smallPrimePowerPairEventMass_eq_zero_of_not_dvd hq hb hqsmall hqdiv]
          exact scaled_pair_density_nonneg K k pa qb
      · have hqlarge : Erdos248.tinyCutoff K < qb.1 := by omega
        have hraw := smallNonTinyDistinctPrimePowerPairEventMass_le_productCoordinateEnergy
          (K := K) (k := k) hA hreg hp hq hpq ha hb hpsmall hqlarge
        have hnorm :
            (Erdos248.intervalStart K : ℝ) /
                ((Erdos248.preSieveModulus K * pa.1 ^ (pa.2 - 1)) *
                  qb.1 ^ qb.2) *
              (16 * primePowerEnergyBracket K) +
              primePowerErrorScale K * 16 =
            16 * primePowerMainScale K *
                ((1 : ℝ) / pa.1 ^ (pa.2 - 1)) *
                ((1 : ℝ) / qb.1 ^ qb.2) +
              16 * primePowerErrorScale K := by
          simpa [primePowerEnergyBracket, primePowerErrorScale, mul_assoc] using
            (pair_event_scale_identity K (pa.1 ^ (pa.2 - 1))
              (qb.1 ^ qb.2) 16 (pow_pos hpPos _) (pow_pos hqPos _))
        calc
          primePowerPairEventMass K k pa.1 pa.2 qb.1 qb.2 ≤
              (Erdos248.intervalStart K : ℝ) /
                  ((Erdos248.preSieveModulus K * pa.1 ^ (pa.2 - 1)) *
                    qb.1 ^ qb.2) *
                (16 * primePowerEnergyBracket K) +
                primePowerErrorScale K * 16 := by
              convert hraw using 1 <;>
                unfold primePowerEnergyBracket primePowerErrorScale <;> ring
          _ = 16 * primePowerMainScale K *
                ((1 : ℝ) / pa.1 ^ (pa.2 - 1)) *
                ((1 : ℝ) / qb.1 ^ qb.2) +
              16 * primePowerErrorScale K := hnorm
          _ ≤ 256 * primePowerMainScale K * primePowerDensity K k pa *
                primePowerDensity K k qb + 256 * primePowerErrorScale K := by
            simp only [one_div]
            have hm := primePowerMainScale_nonneg K
            have he := primePowerErrorScale_nonneg K
            have hd1 : 0 ≤ (1 : ℝ) / pa.1 ^ (pa.2 - 1) := by positivity
            have hd2 : 0 ≤ (1 : ℝ) / qb.1 ^ qb.2 := by positivity
            have hx : 0 ≤ primePowerMainScale K *
                ((1 : ℝ) / pa.1 ^ (pa.2 - 1)) *
                ((1 : ℝ) / qb.1 ^ qb.2) :=
              mul_nonneg (mul_nonneg hm hd1) hd2
            let x := primePowerMainScale K *
              ((1 : ℝ) / pa.1 ^ (pa.2 - 1)) *
              ((1 : ℝ) / qb.1 ^ qb.2)
            have hx' : 0 ≤ x := by simpa [x] using hx
            have hscale : 16 * x + 16 * primePowerErrorScale K ≤
                256 * x + 256 * primePowerErrorScale K := by nlinarith
            simpa [x, one_div, mul_assoc] using hscale
    · rw [smallPrimePowerPairEventMass_eq_zero_of_not_dvd hp ha hpsmall hpdiv]
      exact scaled_pair_density_nonneg K k pa qb
  · have hplarge : Erdos248.tinyCutoff K < pa.1 := by omega
    by_cases hqsmall : qb.1 ≤ Erdos248.tinyCutoff K
    · by_cases hqdiv : qb.1 ∣ k
      · have hraw := smallNonTinyDistinctPrimePowerPairEventMass_le_productCoordinateEnergy
          (K := K) (k := k) hA hreg hq hp (Ne.symm hpq) hb ha hqsmall hplarge
        rw [primePowerPairEventMass_comm K k qb.1 qb.2 pa.1 pa.2] at hraw
        have hnorm :
            (Erdos248.intervalStart K : ℝ) /
                ((Erdos248.preSieveModulus K * qb.1 ^ (qb.2 - 1)) *
                  pa.1 ^ pa.2) *
              (16 * primePowerEnergyBracket K) +
              primePowerErrorScale K * 16 =
            16 * primePowerMainScale K *
                ((1 : ℝ) / qb.1 ^ (qb.2 - 1)) *
                ((1 : ℝ) / pa.1 ^ pa.2) +
              16 * primePowerErrorScale K := by
          simpa [primePowerEnergyBracket, primePowerErrorScale, mul_assoc] using
            (pair_event_scale_identity K (qb.1 ^ (qb.2 - 1))
              (pa.1 ^ pa.2) 16 (pow_pos hqPos _) (pow_pos hpPos _))
        calc
          primePowerPairEventMass K k pa.1 pa.2 qb.1 qb.2 ≤
              (Erdos248.intervalStart K : ℝ) /
                  ((Erdos248.preSieveModulus K * qb.1 ^ (qb.2 - 1)) *
                    pa.1 ^ pa.2) *
                (16 * primePowerEnergyBracket K) +
                primePowerErrorScale K * 16 := by
              convert hraw using 1 <;>
                unfold primePowerEnergyBracket primePowerErrorScale <;> ring
          _ = 16 * primePowerMainScale K *
                ((1 : ℝ) / qb.1 ^ (qb.2 - 1)) *
                ((1 : ℝ) / pa.1 ^ pa.2) +
              16 * primePowerErrorScale K := hnorm
          _ ≤ 256 * primePowerMainScale K * primePowerDensity K k pa *
                primePowerDensity K k qb + 256 * primePowerErrorScale K := by
            simp only [one_div]
            have hm := primePowerMainScale_nonneg K
            have he := primePowerErrorScale_nonneg K
            have hd1 : 0 ≤ (1 : ℝ) / pa.1 ^ pa.2 := by positivity
            have hd2 : 0 ≤ (1 : ℝ) / qb.1 ^ (qb.2 - 1) := by positivity
            have hx : 0 ≤ primePowerMainScale K *
                ((1 : ℝ) / pa.1 ^ pa.2) *
                ((1 : ℝ) / qb.1 ^ (qb.2 - 1)) :=
              mul_nonneg (mul_nonneg hm hd1) hd2
            let x := primePowerMainScale K *
              ((1 : ℝ) / pa.1 ^ pa.2) *
              ((1 : ℝ) / qb.1 ^ (qb.2 - 1))
            have hx' : 0 ≤ x := by simpa [x] using hx
            have hscale : 16 * x + 16 * primePowerErrorScale K ≤
                256 * x + 256 * primePowerErrorScale K := by nlinarith
            simpa [x, one_div, mul_assoc, mul_comm, mul_left_comm] using hscale
      · rw [primePowerPairEventMass_comm K k pa.1 pa.2 qb.1 qb.2,
          smallPrimePowerPairEventMass_eq_zero_of_not_dvd hq hb hqsmall hqdiv]
        exact scaled_pair_density_nonneg K k pa qb
    · have hqlarge : Erdos248.tinyCutoff K < qb.1 := by omega
      have hraw := nonTinyDistinctPrimePowerPairEventMass_le_productCoordinateEnergy
        (K := K) (k := k) hA hreg hp hq hpq
          ((show 0 < 2 by norm_num).trans_le ha)
          ((show 0 < 2 by norm_num).trans_le hb) hplarge hqlarge
      have hnorm :
          (Erdos248.intervalStart K : ℝ) /
              ((Erdos248.preSieveModulus K * pa.1 ^ pa.2) * qb.1 ^ qb.2) *
            (256 * primePowerEnergyBracket K) +
            primePowerErrorScale K * 256 =
          256 * primePowerMainScale K * ((1 : ℝ) / pa.1 ^ pa.2) *
              ((1 : ℝ) / qb.1 ^ qb.2) +
            256 * primePowerErrorScale K := by
        simpa [primePowerEnergyBracket, primePowerErrorScale, mul_assoc] using
          (pair_event_scale_identity K (pa.1 ^ pa.2) (qb.1 ^ qb.2)
            256 (pow_pos hpPos _) (pow_pos hqPos _))
      calc
        primePowerPairEventMass K k pa.1 pa.2 qb.1 qb.2 ≤
            (Erdos248.intervalStart K : ℝ) /
                ((Erdos248.preSieveModulus K * pa.1 ^ pa.2) * qb.1 ^ qb.2) *
              (256 * primePowerEnergyBracket K) +
              primePowerErrorScale K * 256 := by
            convert hraw using 1 <;>
              unfold primePowerEnergyBracket primePowerErrorScale <;> ring
        _ = 256 * primePowerMainScale K * ((1 : ℝ) / pa.1 ^ pa.2) *
              ((1 : ℝ) / qb.1 ^ qb.2) +
            256 * primePowerErrorScale K := hnorm
        _ = 256 * primePowerMainScale K * primePowerDensity K k pa *
              primePowerDensity K k qb + 256 * primePowerErrorScale K := by
          simp [primePowerDensity, hpsmall, hqsmall]

theorem scaled_same_density_nonneg (K k : ℕ) (pa qb : ℕ × ℕ) :
    0 ≤ 16 * primePowerMainScale K * samePrimePowerDensity K k pa qb +
      16 * primePowerErrorScale K := by
  apply add_nonneg
  · exact mul_nonneg
      (mul_nonneg (by norm_num) (primePowerMainScale_nonneg K))
      (samePrimePowerDensity_nonneg K k pa qb)
  · exact mul_nonneg (by norm_num) (primePowerErrorScale_nonneg K)

/-- A same-base pair is one event at the larger exponent.  The corresponding
diagonal density uses that maximum exponent rather than a product density. -/
theorem samePrimePowerPairEventMass_le_density
    {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K k : ℕ} (hreg : Erdos248.NormalizationRegular A K)
    {pa qb : ℕ × ℕ}
    (hpa : pa ∈ properPrimePowerIndices (3 * Erdos248.intervalStart K))
    (hqb : qb ∈ properPrimePowerIndices (3 * Erdos248.intervalStart K))
    (hpq : pa.1 = qb.1) :
    primePowerPairEventMass K k pa.1 pa.2 qb.1 qb.2 ≤
      16 * primePowerMainScale K * samePrimePowerDensity K k pa qb +
        16 * primePowerErrorScale K := by
  have hpdata := mem_properPrimePowerIndices_iff.mp hpa
  have hqdata := mem_properPrimePowerIndices_iff.mp hqb
  have hp : pa.1.Prime := hpdata.2.2.2.2.1
  have ha : 2 ≤ pa.2 := hpdata.2.2.1
  have hb : 2 ≤ qb.2 := hqdata.2.2.1
  have hmax : 2 ≤ max pa.2 qb.2 := ha.trans (le_max_left _ _)
  have hpPos : 0 < pa.1 := hp.pos
  rw [show qb.1 = pa.1 by exact hpq.symm,
    primePowerPairEventMass_same_eq_max]
  by_cases hpsmall : pa.1 ≤ Erdos248.tinyCutoff K
  · by_cases hpdiv : pa.1 ∣ k
    · have hraw := smallPrimePowerEventMass_le_productCoordinateEnergy
        (K := K) (k := k) hA hreg hp hmax hpsmall
      have hnorm :
          (Erdos248.intervalStart K : ℝ) /
              (Erdos248.preSieveModulus K * pa.1 ^ (max pa.2 qb.2 - 1)) *
            primePowerEnergyBracket K + primePowerErrorScale K =
          primePowerMainScale K *
              ((1 : ℝ) / pa.1 ^ (max pa.2 qb.2 - 1)) +
            primePowerErrorScale K := by
        simpa [primePowerEnergyBracket, primePowerErrorScale, mul_assoc] using
          (single_event_scale_identity K (pa.1 ^ (max pa.2 qb.2 - 1)) 1
            (pow_pos hpPos _))
      calc
        primePowerEventMass K k pa.1 (max pa.2 qb.2) ≤
            (Erdos248.intervalStart K : ℝ) /
                (Erdos248.preSieveModulus K * pa.1 ^ (max pa.2 qb.2 - 1)) *
              primePowerEnergyBracket K + primePowerErrorScale K := by
            simpa [primePowerEnergyBracket, primePowerErrorScale] using hraw
        _ = primePowerMainScale K *
              ((1 : ℝ) / pa.1 ^ (max pa.2 qb.2 - 1)) +
            primePowerErrorScale K := hnorm
        _ ≤ 16 * primePowerMainScale K * samePrimePowerDensity K k pa qb +
              16 * primePowerErrorScale K := by
          have hqsmall : qb.1 ≤ Erdos248.tinyCutoff K := hpq ▸ hpsmall
          have hqdiv : qb.1 ∣ k := hpq ▸ hpdiv
          simp only [one_div, ge_iff_le]
          let x := primePowerMainScale K *
            ((1 : ℝ) / pa.1 ^ (max pa.2 qb.2 - 1))
          have hx : 0 ≤ x := by
            dsimp [x]
            exact mul_nonneg (primePowerMainScale_nonneg K) (by positivity)
          have he := primePowerErrorScale_nonneg K
          have hscale : x + primePowerErrorScale K ≤
              16 * x + 16 * primePowerErrorScale K := by nlinarith
          simpa [x, one_div, mul_assoc, hpq.symm] using hscale
    · rw [smallPrimePowerEventMass_eq_zero_of_not_dvd hp hmax hpsmall hpdiv]
      exact scaled_same_density_nonneg K k pa qb
  · have hplarge : Erdos248.tinyCutoff K < pa.1 := by omega
    have hraw := nonTinyPrimePowerEventMass_le_productCoordinateEnergy
      (K := K) (k := k) hA hreg hp ((show 0 < 2 by norm_num).trans_le hmax)
      hplarge
    have hnorm :
        (Erdos248.intervalStart K : ℝ) /
            (Erdos248.preSieveModulus K * pa.1 ^ (max pa.2 qb.2)) *
          (16 * primePowerEnergyBracket K) + primePowerErrorScale K * 16 =
        16 * primePowerMainScale K *
            ((1 : ℝ) / pa.1 ^ (max pa.2 qb.2)) +
          16 * primePowerErrorScale K := by
      simpa [primePowerEnergyBracket, primePowerErrorScale, mul_assoc] using
        (single_event_scale_identity K (pa.1 ^ (max pa.2 qb.2)) 16
          (pow_pos hpPos _))
    calc
      primePowerEventMass K k pa.1 (max pa.2 qb.2) ≤
          (Erdos248.intervalStart K : ℝ) /
              (Erdos248.preSieveModulus K * pa.1 ^ (max pa.2 qb.2)) *
            (16 * primePowerEnergyBracket K) + primePowerErrorScale K * 16 := by
          convert hraw using 1 <;>
            unfold primePowerEnergyBracket primePowerErrorScale <;> ring
      _ = 16 * primePowerMainScale K *
            ((1 : ℝ) / pa.1 ^ (max pa.2 qb.2)) +
          16 * primePowerErrorScale K := hnorm
      _ = 16 * primePowerMainScale K * samePrimePowerDensity K k pa qb +
          16 * primePowerErrorScale K := by
        have hqnotSmall : ¬ qb.1 ≤ Erdos248.tinyCutoff K := by
          rw [← hpq]
          exact hpsmall
        simp [samePrimePowerDensity, hpq, hpsmall, hqnotSmall]

end TaoTeravainen
