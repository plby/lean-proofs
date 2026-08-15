/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.RoughReciprocal
import BoundedGaps.Maynard.MaynardCoprimeHarmonic
import BoundedGaps.Maynard.PreSieveLocalSeries
import BoundedGaps.Maynard.ReciprocalTotientCorrectionEndpoint
import BoundedGaps.Maynard.WirsingAllEndpoints
import Mathlib.NumberTheory.EulerProduct.Basic

/-!
# A uniform harmonic estimate for rough integers

This file connects the rough reciprocal mass arising after divisor switching
to the all-endpoint Wirsing estimate already available in `BoundedGaps`.
The elementary Euler-product lemma below supplies the uniform inequality
`V(D) * log (D+1) <= 1` for the primorial density `V(D)`.
-/

namespace Erdos387

open scoped BigOperators

open Finset Nat Real

namespace RoughHarmonic

/-- The reciprocal function, regarded only as a multiplicative function on
positive natural numbers. -/
private noncomputable def reciprocalNat (n : ℕ) : ℝ := (1 : ℝ) / n

private theorem reciprocalNat_one : reciprocalNat 1 = 1 := by
  simp [reciprocalNat]

private theorem reciprocalNat_mul_of_coprime {m n : ℕ}
    (_h : Nat.Coprime m n) :
    reciprocalNat (m * n) = reciprocalNat m * reciprocalNat n := by
  simp [reciprocalNat]
  ring

private theorem summable_reciprocalNat_primePowers {p : ℕ}
    (hp : p.Prime) :
    Summable (fun e : ℕ => ‖reciprocalNat (p ^ e)‖) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hnorm : ‖(1 : ℝ) / p‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact (div_lt_one (by positivity)).mpr hpR
  simpa [reciprocalNat, one_div, map_pow, norm_pow] using
    (summable_geometric_of_norm_lt_one hnorm)

/-- The harmonic sum through `D` is bounded by the inverse primorial
density.  This is the finite form of the elementary observation that the
Euler product over primes at most `D` contains every integer at most `D`.
-/
theorem harmonic_mul_preSieveSingularSeries_le_one (D : ℕ) :
    (((harmonic D : ℚ) : ℝ) *
      BoundedGaps.Maynard.preSieveSingularSeries D) ≤ 1 := by
  let f : ℕ → ℝ := reciprocalNat
  have hsmooth :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
      (f := f) reciprocalNat_one
      (fun {_m _n} hmn => reciprocalNat_mul_of_coprime hmn)
      (fun {_p} hp => summable_reciprocalNat_primePowers hp) (D + 1)
  have hsummable : Summable (fun m : (D + 1).smoothNumbers => f m) :=
    hsmooth.1.of_norm
  let J := Finset.Icc 1 D
  let embed : J → (D + 1).smoothNumbers := fun n =>
    ⟨n, Nat.mem_smoothNumbers_of_lt
      (zero_lt_one.trans_le (Finset.mem_Icc.mp n.property).1)
      (Nat.lt_succ_of_le (Finset.mem_Icc.mp n.property).2)⟩
  have hinj : Function.Injective embed := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun x : (D + 1).smoothNumbers => (x : ℕ)) hab
  have hfinite : (((harmonic D : ℚ) : ℝ)) ≤
      ∑' m : (D + 1).smoothNumbers, f m := by
    rw [harmonic_eq_sum_Icc]
    simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    calc
      (∑ n ∈ Finset.Icc 1 D, ((n : ℝ))⁻¹) =
          ∑ n ∈ Finset.Icc 1 D, f n := by
        apply Finset.sum_congr rfl
        intro n hn
        simp [f, reciprocalNat, one_div]
      _ = ∑ n : J, f (embed n) := by
        rw [Finset.sum_subtype]
        simp [J]
      _ = ∑ m ∈ (Finset.univ : Finset J).image embed, f m := by
        rw [Finset.sum_image]
        intro a ha b hb hab
        exact hinj hab
      _ ≤ ∑' m : (D + 1).smoothNumbers, f m := by
        exact hsummable.sum_le_tsum _ (fun m hm => by
          simp [f, reciprocalNat])
  have hprod :
      (∏ p ∈ Nat.primesLE D, (1 - (1 : ℝ) / p)⁻¹) =
        ∑' m : (D + 1).smoothNumbers, f m := by
    have hsumEq := hsmooth.2.tsum_eq
    rw [show Nat.primesLE D = (D + 1).primesBelow from rfl]
    calc
      (∏ p ∈ (D + 1).primesBelow, (1 - (1 : ℝ) / p)⁻¹) =
          ∏ p ∈ (D + 1).primesBelow, ∑' e : ℕ, f (p ^ e) := by
        apply Finset.prod_congr rfl
        intro p hp
        have hpPrime := Nat.prime_of_mem_primesBelow hp
        have hpR : (1 : ℝ) < p := by exact_mod_cast hpPrime.one_lt
        rw [show (∑' e : ℕ, f (p ^ e)) =
            ∑' e : ℕ, ((1 : ℝ) / p) ^ e by
          apply tsum_congr
          intro e
          simp [f, reciprocalNat]]
        exact (tsum_geometric_of_norm_lt_one (by
          rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
          exact (div_lt_one (by positivity)).mpr hpR)).symm
      _ = _ := hsumEq.symm
  have hVpos : 0 < BoundedGaps.Maynard.preSieveSingularSeries D := by
    unfold BoundedGaps.Maynard.preSieveSingularSeries
    apply Finset.prod_pos
    intro p hp
    have hpPrime := Nat.prime_of_mem_primesLE hp
    have hpR : (1 : ℝ) < p := by exact_mod_cast hpPrime.one_lt
    exact sub_pos.mpr ((div_lt_one (by positivity)).mpr hpR)
  have hinvprod :
      (∏ p ∈ Nat.primesLE D, (1 - (1 : ℝ) / p)⁻¹) =
        (BoundedGaps.Maynard.preSieveSingularSeries D)⁻¹ := by
    unfold BoundedGaps.Maynard.preSieveSingularSeries
    rw [Finset.prod_inv_distrib]
  rw [← hprod, hinvprod] at hfinite
  calc
    (((harmonic D : ℚ) : ℝ) *
        BoundedGaps.Maynard.preSieveSingularSeries D) ≤
        (BoundedGaps.Maynard.preSieveSingularSeries D)⁻¹ *
          BoundedGaps.Maynard.preSieveSingularSeries D := by
      exact mul_le_mul_of_nonneg_right hfinite hVpos.le
    _ = 1 := inv_mul_cancel₀ hVpos.ne'

/-- An explicit Mertens-type upper bound for the primorial density. -/
theorem log_mul_preSieveSingularSeries_le_one (D : ℕ) :
    Real.log (D + 1 : ℕ) *
      BoundedGaps.Maynard.preSieveSingularSeries D ≤ 1 := by
  have hlog := log_add_one_le_harmonic D
  have hVnonneg : 0 ≤ BoundedGaps.Maynard.preSieveSingularSeries D := by
    rw [BoundedGaps.Maynard.preSieveSingularSeries_eq_totient_div]
    positivity
  exact (mul_le_mul_of_nonneg_right hlog hVnonneg).trans
    (harmonic_mul_preSieveSingularSeries_le_one D)

/-- Being `z`-rough is exactly coprimality to the product of the primes
strictly below `z`. -/
theorem isZRough_iff_coprime_primorial {z m : ℕ} :
    IsZRough z m ↔ Nat.Coprime m (primorial (z - 1)) := by
  constructor
  · intro hrough
    by_contra hnot
    obtain ⟨p, hp, hpm, hpW⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
    have hpBound : p ≤ z - 1 := hp.dvd_primorial_iff.mp hpW
    have hz : 0 < z := hp.pos.trans_le (hpBound.trans (Nat.sub_le z 1))
    have hpz : p < z := hpBound.trans_lt (Nat.sub_lt hz (by norm_num))
    exact hrough p hp hpz hpm
  · intro hcop p hp hpz hpm
    have hpBound : p ≤ z - 1 := le_sub_one_of_lt hpz
    have hpW : p ∣ primorial (z - 1) := hp.dvd_primorial_iff.mpr hpBound
    have hpCop : Nat.Coprime p (primorial (z - 1)) :=
      Nat.Coprime.of_dvd_left hpm hcop
    exact hp.ne_one (hpCop.eq_one_of_dvd hpW)

/-- The named rough reciprocal mass is literally the coprime harmonic sum
for the corresponding primorial. -/
theorem roughReciprocalMass_eq_coprimeHarmonicSum (z T : ℕ) :
    roughReciprocalMass z T =
      BoundedGaps.Maynard.coprimeHarmonicSum (primorial (z - 1)) T := by
  classical
  unfold roughReciprocalMass roughPositiveUpTo
    BoundedGaps.Maynard.coprimeHarmonicSum
  congr 1
  ext m
  simp only [Finset.mem_filter, Finset.mem_Icc]
  rw [isZRough_iff_coprime_primorial]

/-- Uniform all-endpoint upper bound for the rough harmonic mass.  It is
stated with the existing absolute Wirsing constant exposed; the next
corollaries combine it with `V(D) log(D+1) <= 1`.
-/
theorem exists_uniform_roughReciprocalMass_le_wirsing :
    ∃ K : ℝ, 0 < K ∧ ∀ (z T : ℕ), 2 ≤ z →
      roughReciprocalMass z T ≤
        BoundedGaps.Maynard.preSieveSingularSeries (z - 1) * Real.log T +
          10 * BoundedGaps.Maynard.preSieveSingularSeries (z - 1) *
            (K + Real.log (z - 1 : ℕ) +
              BoundedGaps.Maynard.primeLogDivisorMass 1 + Real.log 2) +
          2 * (Real.exp 16 +
            4 * BoundedGaps.Maynard.reciprocalTotientCorrectionQuarterConstant) := by
  obtain ⟨K, hK, hWirsing⟩ :=
    BoundedGaps.Maynard.exists_uniform_abs_squarefreeCoprimeInvTotientMean_sub_density_log_le
  refine ⟨K, hK, ?_⟩
  intro z T hz
  let D := z - 1
  have hsq : Squarefree (primorial D * 1) := by
    simpa using squarefree_primorial D
  have hW := hWirsing (D := D) (P := 1) (Q := T)
    (by norm_num) hsq
  simp only [Nat.mul_one] at hW
  have hcomparison :=
    BoundedGaps.Maynard.abs_squarefreeCoprimeInvTotientMean_sub_coprimeHarmonicSum_le
      (primorial D) T
  have hdensity :
      BoundedGaps.Maynard.coprimeHarmonicDensity (primorial D) =
        BoundedGaps.Maynard.preSieveSingularSeries D := by
    unfold BoundedGaps.Maynard.coprimeHarmonicDensity
    exact (BoundedGaps.Maynard.preSieveSingularSeries_eq_totient_div D).symm
  have hcompLower := (abs_le.mp hcomparison).1
  have hWupper := (abs_le.mp hW).2
  rw [roughReciprocalMass_eq_coprimeHarmonicSum]
  calc
    BoundedGaps.Maynard.coprimeHarmonicSum (primorial D) T ≤
        BoundedGaps.Maynard.squarefreeCoprimeInvTotientMean
            (primorial D) T +
          2 * (Real.exp 16 +
            4 * BoundedGaps.Maynard.reciprocalTotientCorrectionQuarterConstant) := by
      linarith
    _ ≤ BoundedGaps.Maynard.coprimeHarmonicDensity (primorial D) *
            Real.log T +
          10 * BoundedGaps.Maynard.coprimeHarmonicDensity (primorial D) *
            (K + Real.log D +
              BoundedGaps.Maynard.primeLogDivisorMass 1 + Real.log 2) +
          2 * (Real.exp 16 +
            4 * BoundedGaps.Maynard.reciprocalTotientCorrectionQuarterConstant) := by
      linarith
    _ = _ := by simp only [hdensity, D]

/-- The same estimate in the standard sieve form `log T / log z`, obtained
from the elementary density inequality proved above. -/
theorem exists_uniform_roughReciprocalMass_le_log_ratio :
    ∃ K : ℝ, 0 < K ∧ ∀ (z T : ℕ), 2 ≤ z →
      roughReciprocalMass z T ≤
        Real.log T / Real.log z +
          10 * ((K + Real.log (z - 1 : ℕ) +
            BoundedGaps.Maynard.primeLogDivisorMass 1 + Real.log 2) /
              Real.log z) +
          2 * (Real.exp 16 +
            4 * BoundedGaps.Maynard.reciprocalTotientCorrectionQuarterConstant) := by
  obtain ⟨K, hK, hbase⟩ := exists_uniform_roughReciprocalMass_le_wirsing
  refine ⟨K, hK, ?_⟩
  intro z T hz
  have hb := hbase z T hz
  let D := z - 1
  have hDone : 1 ≤ z := by omega
  have hDadd : D + 1 = z := by
    dsimp [D]
    exact Nat.sub_add_cancel hDone
  have hlogzPos : 0 < Real.log (z : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < z by omega)
  have hVL := log_mul_preSieveSingularSeries_le_one D
  have hVle : BoundedGaps.Maynard.preSieveSingularSeries D ≤
      1 / Real.log (z : ℝ) := by
    apply (le_div_iff₀ hlogzPos).2
    simpa [hDadd, mul_comm] using hVL
  have hlogT : 0 ≤ Real.log (T : ℝ) := Real.log_natCast_nonneg T
  have hmass : 0 ≤ BoundedGaps.Maynard.primeLogDivisorMass 1 := by
    unfold BoundedGaps.Maynard.primeLogDivisorMass
    positivity
  have hA : 0 ≤ K + Real.log (D : ℕ) +
      BoundedGaps.Maynard.primeLogDivisorMass 1 + Real.log 2 := by
    have hlogD : 0 ≤ Real.log (D : ℝ) := Real.log_natCast_nonneg D
    have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
    linarith
  have hterm1 :
      BoundedGaps.Maynard.preSieveSingularSeries D * Real.log T ≤
        (1 / Real.log (z : ℝ)) * Real.log T :=
    mul_le_mul_of_nonneg_right hVle hlogT
  have hterm2 :
      BoundedGaps.Maynard.preSieveSingularSeries D *
          (K + Real.log D +
            BoundedGaps.Maynard.primeLogDivisorMass 1 + Real.log 2) ≤
        (1 / Real.log (z : ℝ)) *
          (K + Real.log D +
            BoundedGaps.Maynard.primeLogDivisorMass 1 + Real.log 2) :=
    mul_le_mul_of_nonneg_right hVle hA
  have hterm2' := mul_le_mul_of_nonneg_left hterm2 (show (0 : ℝ) ≤ 10 by norm_num)
  calc
    roughReciprocalMass z T ≤
        BoundedGaps.Maynard.preSieveSingularSeries (z - 1) * Real.log T +
          10 * BoundedGaps.Maynard.preSieveSingularSeries (z - 1) *
            (K + Real.log (z - 1 : ℕ) +
              BoundedGaps.Maynard.primeLogDivisorMass 1 + Real.log 2) +
          2 * (Real.exp 16 +
            4 * BoundedGaps.Maynard.reciprocalTotientCorrectionQuarterConstant) := hb
    _ ≤ (1 / Real.log (z : ℝ)) * Real.log T +
          10 * ((1 / Real.log (z : ℝ)) *
            (K + Real.log (z - 1 : ℕ) +
              BoundedGaps.Maynard.primeLogDivisorMass 1 + Real.log 2)) +
          2 * (Real.exp 16 +
            4 * BoundedGaps.Maynard.reciprocalTotientCorrectionQuarterConstant) := by
      linarith
    _ = _ := by ring

/-- The explicit right-hand side of the uniform rough harmonic estimate. -/
noncomputable def roughLogRatioEnvelope (K : ℝ) (z T : ℕ) : ℝ :=
  Real.log T / Real.log z +
    10 * ((K + Real.log (z - 1 : ℕ) +
      BoundedGaps.Maynard.primeLogDivisorMass 1 + Real.log 2) /
        Real.log z) +
    2 * (Real.exp 16 +
      4 * BoundedGaps.Maynard.reciprocalTotientCorrectionQuarterConstant)

theorem exists_uniform_roughReciprocalMass_le_envelope :
    ∃ K : ℝ, 0 < K ∧ ∀ (z T : ℕ), 2 ≤ z →
      roughReciprocalMass z T ≤ roughLogRatioEnvelope K z T := by
  simpa only [roughLogRatioEnvelope] using
    exists_uniform_roughReciprocalMass_le_log_ratio

end RoughHarmonic

namespace CoverBPZ

/-- Proposition 6.2 in the form directly consumed by the large-component
error count: the switched tuple main sum is bounded by a fixed power of the
uniform `log T / log z` envelope, with the finite CRT endpoint retained.
-/
theorem exists_uniform_refinedLargeErrors_card_le_logRatioEnvelope :
    ∃ C : ℝ, 0 < C ∧
      ∀ {B K X z large : ℕ} (S : BPZSection6Input B K),
        0 < B → 2 * S.k ≤ z →
        6 * S.k ≤ X →
        (X / (large + 1)) ^ 2 ≤ X / 2 →
        ((RefinedLargeErrors S X z large).card : ℝ) ≤
          (((X - X / 2 : ℕ) : ℝ) / refinementModulus S) *
              (RoughHarmonic.roughLogRatioEnvelope C z
                (X / (large + 1))) ^ S.k +
            2 * ((X / (large + 1) + 1) ^ S.k : ℕ) := by
  obtain ⟨C, hC, hmass⟩ :=
    RoughHarmonic.exists_uniform_roughReciprocalMass_le_envelope
  refine ⟨C, hC, ?_⟩
  intro B K X z large S hB hz hXwide hscale
  have hbase := refinedLargeErrors_card_le_roughMassPow_add_endpoint
    S hB hz hXwide hscale
  have hzTwo : 2 ≤ z := by
    have hk3 := S.hk3
    exact (show 2 ≤ 2 * S.k by omega).trans hz
  have hrough := hmass z (X / (large + 1)) hzTwo
  have hmassNonneg : 0 ≤ roughReciprocalMass z (X / (large + 1)) := by
    unfold roughReciprocalMass
    positivity
  have hpow :
      (roughReciprocalMass z (X / (large + 1))) ^ S.k ≤
        (RoughHarmonic.roughLogRatioEnvelope C z
          (X / (large + 1))) ^ S.k :=
    pow_le_pow_left₀ hmassNonneg hrough S.k
  have hcoef : 0 ≤
      (((X - X / 2 : ℕ) : ℝ) / refinementModulus S) := by
    positivity
  exact hbase.trans (add_le_add
    (mul_le_mul_of_nonneg_left hpow hcoef) le_rfl)

end CoverBPZ

end Erdos387
