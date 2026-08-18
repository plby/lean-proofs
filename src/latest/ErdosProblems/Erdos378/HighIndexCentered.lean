/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos378.RelaxedChebyshev
import ErdosProblems.Erdos378.WeightedCircleEquidistribution
import ErdosProblems.Erdos378.InverseSquareExceptionalArc

/-!
# Centered prime sums for the high-index argument

This file connects the uniform reciprocal exponential-sum estimates to the
centered fractional-part identities in Granville--Ramaré Propositions 3.1
and 3.3.  The common bridge is a weighted Weyl criterion on `ℝ / ℤ`.
-/

open Filter Set
open scoped Topology BigOperators ENNReal NNReal ComplexConjugate

namespace Erdos378
namespace HighIndexCentered

open CircleEquidistribution
open WeightedCircleEquidistribution
open PrimeReciprocal
open PrimeWeightedInterval
open ReciprocalExponential
open HighIndexChebyshev
open HighIndexCutoffs
open RelaxedChebyshev

noncomputable section

def primeIntervalSet (a b : ℕ) : Finset ℕ :=
  (Finset.Ioc a b).filter Nat.Prime

def primeIntervalLogMass (a b : ℕ) : ℝ :=
  ∑ p ∈ primeIntervalSet a b, Real.log (p : ℝ)

def primeLogWeight (p : ℕ) : ℝ≥0 :=
  ⟨Real.log (p : ℝ), Real.log_natCast_nonneg p⟩

@[simp, norm_cast] lemma coe_primeLogWeight (p : ℕ) :
    (primeLogWeight p : ℝ) = Real.log (p : ℝ) := rfl

def reciprocalCirclePoint (X p : ℕ) : UnitCircle :=
  ((-((X : ℝ) / (p : ℝ)) : ℝ) : UnitCircle)

def centeredReciprocalPrimeSum (a b X : ℕ) : ℝ :=
  ∑ p ∈ primeIntervalSet a b,
    Real.log (p : ℝ) * centeredCoord (reciprocalCirclePoint X p)

lemma centeredCoord_reciprocalCirclePoint_of_not_dvd
    {X p : ℕ} (hp : 0 < p) (hpd : ¬p ∣ X) :
    centeredCoord (reciprocalCirclePoint X p) =
      1 / 2 - ((X % p : ℕ) : ℝ) / (p : ℝ) := by
  have hmod : X % p ≠ 0 := by
    exact fun hz ↦ hpd (Nat.dvd_iff_mod_eq_zero.mpr hz)
  have hfract : Int.fract ((X : ℝ) / (p : ℝ)) ≠ 0 := by
    rw [Int.fract_div_natCast_eq_div_natCast_mod]
    exact div_ne_zero (by exact_mod_cast hmod) (by exact_mod_cast hp.ne')
  unfold centeredCoord reciprocalCirclePoint
  rw [unitCoord_coe, Int.fract_neg hfract,
    Int.fract_div_natCast_eq_div_natCast_mod]
  ring

def divisorPrimeLogMass (s : Finset ℕ) (X : ℕ) : ℝ :=
  ∑ p ∈ s.filter (fun p ↦ p ∣ X), Real.log (p : ℝ)

lemma divisorPrimeLogMass_le_log {s : Finset ℕ} {X : ℕ} (hX : 0 < X)
    (hs : ∀ p ∈ s, p.Prime) :
    divisorPrimeLogMass s X ≤ Real.log (X : ℝ) := by
  have hsub : s.filter (fun p ↦ p ∣ X) ⊆ X.primeFactors := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hps, hpX⟩
    exact Nat.mem_primeFactors.mpr ⟨hs p hps, hpX, hX.ne'⟩
  have hsum : divisorPrimeLogMass s X ≤
      ∑ p ∈ X.primeFactors, Real.log (p : ℝ) := by
    unfold divisorPrimeLogMass
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro p hp hpnot
    exact Real.log_nonneg (by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le)
  have hprodPos : 0 < ∏ p ∈ X.primeFactors, p := by
    apply Finset.prod_pos
    intro p hp
    exact Nat.pos_of_mem_primeFactors hp
  have hprodLe : ∏ p ∈ X.primeFactors, p ≤ X :=
    Nat.le_of_dvd hX (Nat.prod_primeFactors_dvd X)
  calc
    divisorPrimeLogMass s X ≤
        ∑ p ∈ X.primeFactors, Real.log (p : ℝ) := hsum
    _ = Real.log ((∏ p ∈ X.primeFactors, p : ℕ) : ℝ) := by
      rw [← Real.log_prod]
      · norm_num
      · intro p hp
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    _ ≤ Real.log (X : ℝ) :=
      Real.log_le_log (by exact_mod_cast hprodPos) (by exact_mod_cast hprodLe)

lemma coe_totalWeight_primeInterval (a b : ℕ) :
    (totalWeight (primeIntervalSet a b) primeLogWeight : ℝ) =
      primeIntervalLogMass a b := by
  simp [totalWeight, primeIntervalLogMass]

lemma normalizedCenteredAverage_primeInterval (a b X : ℕ) :
    normalizedCenteredAverage (primeIntervalSet a b) primeLogWeight
        (reciprocalCirclePoint X) =
      (primeIntervalLogMass a b)⁻¹ * centeredReciprocalPrimeSum a b X := by
  simp only [normalizedCenteredAverage, coe_totalWeight_primeInterval,
    centeredReciprocalPrimeSum, coe_primeLogWeight]

lemma fourier_reciprocalCirclePoint_ofNat (h X p : ℕ) :
    fourier (h : ℤ) (reciprocalCirclePoint X p) =
      reciprocalWeight (((h * X : ℕ) : ℝ)) p := by
  unfold reciprocalCirclePoint reciprocalWeight ReciprocalExponential.e
  rw [fourier_coe_apply]
  norm_num
  congr 1
  push_cast
  ring

lemma prime_fourier_sum_ofNat (a b h X : ℕ) :
    (∑ p ∈ primeIntervalSet a b,
        ((primeLogWeight p : ℝ) : ℂ) *
          fourier (h : ℤ) (reciprocalCirclePoint X p)) =
      primeWeightedInterval (reciprocalWeight (((h * X : ℕ) : ℝ))) a b := by
  unfold primeIntervalSet primeWeightedInterval
  apply Finset.sum_congr rfl
  intro p hp
  rw [fourier_reciprocalCirclePoint_ofNat]
  rfl

lemma prime_fourier_sum_neg_ofNat (a b h X : ℕ) :
    (∑ p ∈ primeIntervalSet a b,
        ((primeLogWeight p : ℝ) : ℂ) *
          fourier (-(h : ℤ)) (reciprocalCirclePoint X p)) =
      conj (primeWeightedInterval
        (reciprocalWeight (((h * X : ℕ) : ℝ))) a b) := by
  calc
    _ = ∑ p ∈ primeIntervalSet a b,
        conj (((primeLogWeight p : ℝ) : ℂ) *
          fourier (h : ℤ) (reciprocalCirclePoint X p)) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [fourier_neg, map_mul]
      congr 1
      simpa only [coe_primeLogWeight] using
        (Complex.conj_ofReal (Real.log (p : ℝ))).symm
    _ = conj (∑ p ∈ primeIntervalSet a b,
        ((primeLogWeight p : ℝ) : ℂ) *
          fourier (h : ℤ) (reciprocalCirclePoint X p)) := by
      simp only [map_sum]
    _ = _ := congrArg conj (prime_fourier_sum_ofNat a b h X)

lemma norm_prime_fourier_sum (a b X : ℕ) {h : ℤ} (hh : h ≠ 0) :
    ‖∑ p ∈ primeIntervalSet a b,
        ((primeLogWeight p : ℝ) : ℂ) *
          fourier h (reciprocalCirclePoint X p)‖ =
      ‖primeWeightedInterval
        (reciprocalWeight (((h.natAbs * X : ℕ) : ℝ))) a b‖ := by
  by_cases hnonneg : 0 ≤ h
  · have heq : h = (h.natAbs : ℤ) :=
      (Int.natAbs_of_nonneg hnonneg).symm
    rw [heq, prime_fourier_sum_ofNat]
    simp
  · have hnonpos : h ≤ 0 := le_of_not_ge hnonneg
    have heq : h = -(h.natAbs : ℤ) := by
      have ht := Int.natAbs_of_nonneg (neg_nonneg.mpr hnonpos)
      rw [Int.natAbs_neg] at ht
      omega
    rw [heq, prime_fourier_sum_neg_ofNat]
    simp

theorem tendsto_normalizedCenteredPrimeInterval_of_modes
    {I : Type*} {F : Filter I} (a b X : I → ℕ)
    (hmass : ∀ᶠ i in F, 0 < primeIntervalLogMass (a i) (b i))
    (hmode : ∀ h : ℕ, 0 < h → Tendsto (fun i ↦
      ‖primeWeightedInterval (reciprocalWeight (((h * X i : ℕ) : ℝ)))
        (a i) (b i)‖ / primeIntervalLogMass (a i) (b i)) F (nhds 0)) :
    Tendsto (fun i ↦
      (primeIntervalLogMass (a i) (b i))⁻¹ *
        centeredReciprocalPrimeSum (a i) (b i) (X i)) F (nhds 0) := by
  have hweight : ∀ᶠ i in F,
      totalWeight (primeIntervalSet (a i) (b i)) primeLogWeight ≠ 0 := by
    filter_upwards [hmass] with i hi
    intro hz
    have hzR := congrArg (fun z : ℝ≥0 ↦ (z : ℝ)) hz
    rw [coe_totalWeight_primeInterval, NNReal.coe_zero] at hzR
    linarith
  have hfourier : ∀ h : ℤ, h ≠ 0 → Tendsto
      (fun i ↦ normalizedFourierAverage
        (primeIntervalSet (a i) (b i)) primeLogWeight
          (reciprocalCirclePoint (X i)) h) F (nhds 0) := by
    intro h hh
    have habs : 0 < h.natAbs := Int.natAbs_pos.mpr hh
    have hm := hmode h.natAbs habs
    rw [Metric.tendsto_nhds] at hm ⊢
    intro ε hε
    filter_upwards [hm ε hε, hmass] with i hi hmassI
    rw [dist_zero_right] at hi
    rw [dist_zero_right]
    have hi' : ‖primeWeightedInterval
        (reciprocalWeight (((h.natAbs * X i : ℕ) : ℝ)))
          (a i) (b i)‖ / primeIntervalLogMass (a i) (b i) < ε := by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (div_nonneg (norm_nonneg _) hmassI.le)] at hi
      exact hi
    unfold normalizedFourierAverage
    rw [show (totalWeight (primeIntervalSet (a i) (b i))
        primeLogWeight : ℝ) = primeIntervalLogMass (a i) (b i) by
      exact coe_totalWeight_primeInterval _ _]
    rw [norm_mul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hmassI,
      norm_prime_fourier_sum _ _ _ hh]
    simpa [div_eq_inv_mul] using hi'
  have hcenter := tendsto_weightedCenteredAverage_of_fourier
    (fun i ↦ primeIntervalSet (a i) (b i))
    (fun _i ↦ primeLogWeight)
    (fun i ↦ reciprocalCirclePoint (X i)) hweight hfourier
  simpa only [normalizedCenteredAverage_primeInterval] using hcenter

theorem tendsto_normalizedCenteredPrimeInterval_central
    {I : Type*} {F : Filter I} (a b X : I → ℕ) {C : ℝ} (hC : 0 < C)
    (hbTop : Tendsto b F atTop)
    (hgeom : ∀ᶠ i in F,
      a i < b i ∧ b i ≤ 2 * a i ∧ 0 < X i ∧
      (b i : ℝ) ^ 2 ≤ 4 * X i ∧ X i ≤ b i ^ 15 ∧
      (b i : ℝ) / C ≤ primeIntervalLogMass (a i) (b i)) :
    Tendsto (fun i ↦
      (primeIntervalLogMass (a i) (b i))⁻¹ *
        centeredReciprocalPrimeSum (a i) (b i) (X i)) F (nhds 0) := by
  apply tendsto_normalizedCenteredPrimeInterval_of_modes a b X
  · filter_upwards [hgeom, hbTop.eventually (eventually_gt_atTop 0)] with i hi hb
    exact lt_of_lt_of_le (div_pos (by exact_mod_cast hb) hC) hi.2.2.2.2.2
  · intro h hh
    have hhB : ∀ᶠ i in F, h ≤ b i :=
      hbTop.eventually (eventually_ge_atTop h)
    have hbound := hbTop.eventually
      PrimeWeightedInterval.eventually_centralPrime_bound
    have hlim : Tendsto (fun i ↦
        C * (PrimeWeightedInterval.centralPrimeMajorant (b i) / (b i : ℝ)))
        F (nhds 0) := by
      simpa only [Function.comp_apply, mul_zero] using
        (PrimeWeightedInterval.tendsto_centralPrimeMajorant_div_zero
          |>.comp hbTop).const_mul C
    have hn : ∀ᶠ i in F, 0 ≤
        ‖primeWeightedInterval (reciprocalWeight (((h * X i : ℕ) : ℝ)))
          (a i) (b i)‖ / primeIntervalLogMass (a i) (b i) := by
      filter_upwards [hgeom, hbTop.eventually (eventually_gt_atTop 0)] with i hi hb
      exact div_nonneg (norm_nonneg _)
        (le_trans (div_pos (by exact_mod_cast hb) hC).le hi.2.2.2.2.2)
    have hu : ∀ᶠ i in F,
        ‖primeWeightedInterval (reciprocalWeight (((h * X i : ℕ) : ℝ)))
          (a i) (b i)‖ / primeIntervalLogMass (a i) (b i) ≤
          C * (PrimeWeightedInterval.centralPrimeMajorant (b i) / (b i : ℝ)) := by
      filter_upwards [hgeom, hhB, hbound,
        hbTop.eventually (eventually_gt_atTop 0)] with i hi hhb hprime hb
      rcases hi with ⟨hab, hba, hX, hXlo, hX15, hmass⟩
      have hhpos : 0 < h := hh
      have hfreq : (0 : ℝ) < ((h * X i : ℕ) : ℝ) := by positivity
      have hlo : (b i : ℝ) ^ 2 ≤ 4 * ((h * X i : ℕ) : ℝ) := by
        push_cast
        nlinarith [show (1 : ℝ) ≤ h by exact_mod_cast hh]
      have hhiNat : h * X i ≤ b i ^ 16 := by
        calc
          h * X i ≤ b i * b i ^ 15 := Nat.mul_le_mul hhb hX15
          _ = b i ^ 16 := by ring
      have hnorm := hprime hab hba hfreq hlo (by exact_mod_cast hhiNat)
      have hbR : (0 : ℝ) < b i := by exact_mod_cast hb
      have hscale : (0 : ℝ) < (b i : ℝ) / C := div_pos hbR hC
      have hmaj : 0 ≤ PrimeWeightedInterval.centralPrimeMajorant (b i) := by
        unfold PrimeWeightedInterval.centralPrimeMajorant
          CentralChebyshev.centralChebyshevMajorant
        exact add_nonneg (add_nonneg (add_nonneg
          (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg
            (mul_nonneg (by norm_num) (Real.log_natCast_nonneg _))
            (CentralChebyshevApplication.centralTypeBound_nonneg _)))
          (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg
            (Real.log_natCast_nonneg _)
            (CentralChebyshevApplication.centralTypeBound_nonneg _))))
          (mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)))
          (sub_nonneg.mpr (Chebyshev.theta_le_psi _))
      calc
        _ ≤ PrimeWeightedInterval.centralPrimeMajorant (b i) /
            ((b i : ℝ) / C) := by gcongr
        _ = C * (PrimeWeightedInterval.centralPrimeMajorant (b i) / (b i : ℝ)) := by
          field_simp
    exact squeeze_zero' hn hu hlim

theorem tendsto_normalizedCenteredPrimeInterval_relaxed
    {I : Type*} {F : Filter I} (a b X : I → ℕ) {C : ℝ} (hC : 0 < C)
    (hbTop : Tendsto b F atTop)
    (hgeom : ∀ᶠ i in F,
      a i < b i ∧ b i ≤ 2 * a i ∧ 0 < X i ∧
      (b i : ℝ) ^ 2 ≤ 4 * (farSeparation (b i) : ℝ) ^ 2 * X i ∧
      X i ≤ b i ^ 15 ∧
      (b i : ℝ) /
          (C * Real.log (b i : ℝ) ^ 16) ≤
        primeIntervalLogMass (a i) (b i)) :
    Tendsto (fun i ↦
      (primeIntervalLogMass (a i) (b i))⁻¹ *
        centeredReciprocalPrimeSum (a i) (b i) (X i)) F (nhds 0) := by
  have hlogpos : ∀ᶠ i in F, 0 < Real.log (b i : ℝ) := by
    filter_upwards [hbTop.eventually (eventually_gt_atTop 1)] with i hi
    exact Real.log_pos (by exact_mod_cast hi)
  apply tendsto_normalizedCenteredPrimeInterval_of_modes a b X
  · filter_upwards [hgeom, hbTop.eventually (eventually_gt_atTop 0),
      hlogpos] with i hi hb hlog
    exact lt_of_lt_of_le
      (div_pos (by exact_mod_cast hb) (mul_pos hC (pow_pos hlog 16)))
      hi.2.2.2.2.2
  · intro h hh
    have hhB : ∀ᶠ i in F, h ≤ b i :=
      hbTop.eventually (eventually_ge_atTop h)
    have hbound := hbTop.eventually
      RelaxedChebyshev.eventually_relaxedNearPrime_bound
    have hlim : Tendsto (fun i ↦ C *
        (Real.log (b i : ℝ) ^ 16 *
          (RelaxedChebyshev.relaxedNearPrimeMajorant (b i) / (b i : ℝ))))
        F (nhds 0) := by
      simpa only [Function.comp_apply, mul_zero] using
        (RelaxedChebyshev.tendsto_relaxedNearPrimeMajorant_scaled_zero
          |>.comp hbTop).const_mul C
    have hn : ∀ᶠ i in F, 0 ≤
        ‖primeWeightedInterval (reciprocalWeight (((h * X i : ℕ) : ℝ)))
          (a i) (b i)‖ / primeIntervalLogMass (a i) (b i) := by
      filter_upwards [hgeom, hbTop.eventually (eventually_gt_atTop 0),
        hlogpos] with i hi hb hlog
      exact div_nonneg (norm_nonneg _) (le_trans
        (div_pos (by exact_mod_cast hb) (mul_pos hC (pow_pos hlog 16))).le
        hi.2.2.2.2.2)
    have hu : ∀ᶠ i in F,
        ‖primeWeightedInterval (reciprocalWeight (((h * X i : ℕ) : ℝ)))
            (a i) (b i)‖ / primeIntervalLogMass (a i) (b i) ≤
          C * (Real.log (b i : ℝ) ^ 16 *
            (RelaxedChebyshev.relaxedNearPrimeMajorant (b i) / (b i : ℝ))) := by
      filter_upwards [hgeom, hhB, hbound,
        hbTop.eventually (eventually_gt_atTop 1)] with i hi hhb hprime hb
      rcases hi with ⟨hab, hba, hX, hXlo, hX15, hmass⟩
      have hfreq : (0 : ℝ) < ((h * X i : ℕ) : ℝ) := by positivity
      have hlo : (b i : ℝ) ^ 2 ≤
          4 * (farSeparation (b i) : ℝ) ^ 2 * ((h * X i : ℕ) : ℝ) := by
        push_cast
        nlinarith [show (1 : ℝ) ≤ h by exact_mod_cast hh]
      have hhiNat : h * X i ≤ b i ^ 16 := by
        calc
          h * X i ≤ b i * b i ^ 15 := Nat.mul_le_mul hhb hX15
          _ = b i ^ 16 := by ring
      have hnorm := hprime hab hba hfreq hlo (by exact_mod_cast hhiNat)
      have hbR : (0 : ℝ) < b i := by exact_mod_cast (show 0 < b i by omega)
      have hlog : 0 < Real.log (b i : ℝ) := Real.log_pos (by exact_mod_cast hb)
      have hscale : 0 < (C * Real.log (b i : ℝ) ^ 16) :=
        mul_pos hC (pow_pos hlog 16)
      have hmaj := RelaxedChebyshev.relaxedNearPrimeMajorant_nonneg (b i)
      calc
        _ ≤ RelaxedChebyshev.relaxedNearPrimeMajorant (b i) /
            ((b i : ℝ) / (C * Real.log (b i : ℝ) ^ 16)) := by gcongr
        _ = C * (Real.log (b i : ℝ) ^ 16 *
            (RelaxedChebyshev.relaxedNearPrimeMajorant (b i) / (b i : ℝ))) := by
          field_simp
    exact squeeze_zero' hn hu hlim

/-! ## The fixed source window -/

structure SourcePhaseDatum where
  k : ℕ
  X : ℕ
  hkX : k ≤ X
  hX : X ≤ ReciprocalPrimeSelection.sourcePrimeUpper k ^ 15

def sourcePhaseFilter : Filter SourcePhaseDatum :=
  Filter.comap SourcePhaseDatum.k atTop

lemma tendsto_sourceDatum_k_atTop :
    Tendsto SourcePhaseDatum.k sourcePhaseFilter atTop := by
  rw [tendsto_def]
  exact Filter.map_comap_le

lemma source_primeIntervalLogMass (k : ℕ) :
    primeIntervalLogMass (Nat.sqrt k)
        (ReciprocalPrimeSelection.sourcePrimeUpper k) =
      ReciprocalPrimeSelection.sourcePrimeLogMass k := by
  rfl

lemma primeIntervalLogMass_eq_theta_sub {a b : ℕ} (hab : a ≤ b) :
    primeIntervalLogMass a b =
      Chebyshev.theta (b : ℝ) - Chebyshev.theta (a : ℝ) := by
  have hadd :
      (∑ p ∈ (Finset.Ioc 0 a).filter Nat.Prime, Real.log (p : ℝ)) +
        ∑ p ∈ (Finset.Ioc a b).filter Nat.Prime, Real.log (p : ℝ) =
      ∑ p ∈ (Finset.Ioc 0 b).filter Nat.Prime, Real.log (p : ℝ) := by
    simp_rw [Finset.sum_filter]
    rw [← Finset.sum_union]
    · rw [Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) hab]
    · rw [Finset.disjoint_left]
      intro p hp₁ hp₂
      have h₁ := Finset.mem_Ioc.mp hp₁
      have h₂ := Finset.mem_Ioc.mp hp₂
      omega
  unfold primeIntervalLogMass primeIntervalSet Chebyshev.theta
  simp only [Nat.floor_natCast]
  linarith

theorem eventually_near_primeLogMass_lower :
    ∀ᶠ y : ℕ in atTop, ∀ x : ℕ,
      x < y → y ≤ 2 * x →
      (y : ℝ) / (10000000 * Real.log (y : ℝ) ^ 16) ≤ y - x →
      (y : ℝ) / (100000000 * Real.log (y : ℝ) ^ 16) ≤
        primeIntervalLogMass x y := by
  have herr := Erdos49.Analytic.eventually_mediumTheta_error_div_log_pow
    16 (show (0 : ℝ) < 1 / 1000000000000000 by norm_num)
  rcases herr.exists_forall_of_atTop with ⟨R, hR⟩
  obtain ⟨B₀, hB₀⟩ := exists_nat_ge (max R 4)
  refine Filter.eventually_atTop.2 ⟨2 * B₀, ?_⟩
  intro y hy x hxy hyx hgap
  have hB₀y : B₀ ≤ y := by omega
  have hB₀x : B₀ ≤ x := by omega
  have hRreal : R ≤ (B₀ : ℝ) :=
    (le_max_left R 4).trans (by exact_mod_cast hB₀)
  have hxR : R ≤ (x : ℝ) := hRreal.trans (by exact_mod_cast hB₀x)
  have hyR : R ≤ (y : ℝ) := hRreal.trans (by exact_mod_cast hB₀y)
  have hex := hR (x : ℝ) hxR
  have hey := hR (y : ℝ) hyR
  let Gx : ℝ := Real.log (x : ℝ)
  let Gy : ℝ := Real.log (y : ℝ)
  have hB4 : 4 ≤ B₀ := by
    have hB4R : (4 : ℝ) ≤ B₀ := (le_max_right R 4).trans hB₀
    exact_mod_cast hB4R
  have hx4 : 4 ≤ x := hB4.trans hB₀x
  have hy4 : 4 ≤ y := hx4.trans hxy.le
  have hGx : 1 ≤ Gx := by
    simpa only [Gx] using BoundedGaps.Maynard.one_le_log_natCast hx4
  have hGy : 1 ≤ Gy := by
    simpa only [Gy] using BoundedGaps.Maynard.one_le_log_natCast hy4
  have hyxSq : y ≤ x ^ 2 := by
    calc
      y ≤ 2 * x := hyx
      _ ≤ x ^ 2 := by nlinarith
  have hlog : Gy ≤ 2 * Gx := by
    have hcast : (y : ℝ) ≤ (x : ℝ) ^ 2 := by exact_mod_cast hyxSq
    have ht := Real.log_le_log (by positivity : (0 : ℝ) < y) hcast
    rw [Real.log_pow] at ht
    simpa only [Gy, Gx, Nat.cast_ofNat] using ht
  have hpow : Gy ^ 16 ≤ 2 ^ 16 * Gx ^ 16 := by
    calc
      Gy ^ 16 ≤ (2 * Gx) ^ 16 := by gcongr
      _ = 2 ^ 16 * Gx ^ 16 := by ring
  have hscaleX : (x : ℝ) / Gx ^ 16 ≤
      2 ^ 16 * ((y : ℝ) / Gy ^ 16) := by
    have hGxpos : 0 < Gx ^ 16 := pow_pos (by positivity) 16
    have hGypos : 0 < Gy ^ 16 := pow_pos (by positivity) 16
    rw [div_le_iff₀ hGxpos]
    rw [show 2 ^ 16 * ((y : ℝ) / Gy ^ 16) * Gx ^ 16 =
        (2 ^ 16 * (y : ℝ) * Gx ^ 16) / Gy ^ 16 by ring]
    rw [le_div_iff₀ hGypos]
    calc
      (x : ℝ) * Gy ^ 16 ≤ (y : ℝ) * Gy ^ 16 := by gcongr
      _ ≤ (y : ℝ) * (2 ^ 16 * Gx ^ 16) := by gcongr
      _ = 2 ^ 16 * (y : ℝ) * Gx ^ 16 := by ring
  have hex' : |Chebyshev.theta (x : ℝ) - x| ≤
      (1 / 1000000000000000 : ℝ) *
        (2 ^ 16 * ((y : ℝ) / Gy ^ 16)) := by
    calc
      _ ≤ (1 / 1000000000000000 : ℝ) * ((x : ℝ) / Gx ^ 16) := by
        dsimp only [Gx]
        convert hex using 1 <;> ring
      _ ≤ (1 / 1000000000000000 : ℝ) *
          (2 ^ 16 * ((y : ℝ) / Gy ^ 16)) :=
        mul_le_mul_of_nonneg_left hscaleX (by norm_num)
  have hey' : |Chebyshev.theta (y : ℝ) - y| ≤
      (1 / 1000000000000000 : ℝ) * ((y : ℝ) / Gy ^ 16) := by
    calc
      _ ≤ (1 / 1000000000000000 : ℝ) * (y : ℝ) /
          Real.log (y : ℝ) ^ 16 := hey
      _ = _ := by dsimp only [Gy]; ring
  rw [primeIntervalLogMass_eq_theta_sub hxy.le]
  rcases abs_le.mp hex' with ⟨_hexLo, hexHi⟩
  rcases abs_le.mp hey' with ⟨heyLo, _heyHi⟩
  dsimp only [Gy] at hexHi heyLo
  have hscalePos : 0 < (y : ℝ) / Real.log (y : ℝ) ^ 16 := by positivity
  let S : ℝ := (y : ℝ) / Real.log (y : ℝ) ^ 16
  have hgap' : S / 10000000 ≤ (y : ℝ) - x := by
    dsimp only [S]
    convert hgap using 1 <;> ring
  have hout : S / 100000000 ≤
      Chebyshev.theta (y : ℝ) - Chebyshev.theta (x : ℝ) := by
    dsimp only [S] at hgap' ⊢
    nlinarith
  convert hout using 1 <;> dsimp only [S] <;> ring

lemma eventually_const_mul_log_sixteen_le :
    ∀ᶠ y : ℕ in atTop,
      4194304 * Real.log (y : ℝ) ^ 16 ≤ (y : ℝ) := by
  have hraw := ReciprocalChebyshevAsymptotic.tendsto_log_natCast_rpow_div_rpow
    (16 : ℝ) 1 (by norm_num)
  have hlim : Tendsto (fun y : ℕ ↦
      Real.log (y : ℝ) ^ 16 / (y : ℝ)) atTop (nhds 0) := by
    apply hraw.congr'
    filter_upwards with y
    rw [Real.rpow_one]
    congr 1
    exact Real.rpow_natCast _ 16
  have hsmall := hlim.eventually
    (Iic_mem_nhds (show (0 : ℝ) < 1 / 4194304 by norm_num))
  filter_upwards [hsmall, eventually_gt_atTop 0] with y hy hypos
  have hyR : (0 : ℝ) < y := by exact_mod_cast hypos
  rw [div_le_iff₀ hyR] at hy
  nlinarith

lemma eventually_const_mul_log_pow_le (C : ℝ) (hC : 0 < C) (e : ℕ) :
    ∀ᶠ y : ℕ in atTop,
      C * Real.log (y : ℝ) ^ e ≤ (y : ℝ) := by
  have hraw := ReciprocalChebyshevAsymptotic.tendsto_log_natCast_rpow_div_rpow
    (e : ℝ) 1 (by norm_num)
  have hlim : Tendsto (fun y : ℕ ↦
      Real.log (y : ℝ) ^ e / (y : ℝ)) atTop (nhds 0) := by
    apply hraw.congr'
    filter_upwards with y
    rw [Real.rpow_one]
    congr 1
    exact Real.rpow_natCast _ e
  have hsmall := hlim.eventually
    (Iic_mem_nhds (show (0 : ℝ) < 1 / C by positivity))
  filter_upwards [hsmall, eventually_gt_atTop 0] with y hy hypos
  have hyR : (0 : ℝ) < y := by exact_mod_cast hypos
  rw [div_le_iff₀ hyR] at hy
  have hC0 : (C : ℝ) ≠ 0 := hC.ne'
  calc
    C * Real.log (y : ℝ) ^ e ≤ C * ((1 / C) * (y : ℝ)) := by gcongr
    _ = (y : ℝ) := by field_simp

theorem eventually_near_sqrt_gap_lower :
    ∀ᶠ k : ℕ in atTop, ∀ n : ℕ,
      k ≤ n / 2 →
      (n : ℝ) <
        (farSeparation (ReciprocalPrimeSelection.sourcePrimeUpper k) : ℝ) ^ 2 *
          (ReciprocalPrimeSelection.sourcePrimeUpper k : ℝ) ^ 2 →
      (Nat.sqrt n : ℝ) /
          (10000000 * Real.log (Nat.sqrt n : ℝ) ^ 16) ≤
        (Nat.sqrt n : ℝ) - Nat.sqrt (n - k) := by
  have hsTop : Tendsto (fun k : ℕ ↦ Nat.sqrt k) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro B
    exact ⟨B ^ 2, fun k hk ↦ Nat.le_sqrt'.mpr hk⟩
  rcases eventually_const_mul_log_sixteen_le.exists_forall_of_atTop with
    ⟨Y₀, hY₀⟩
  filter_upwards [hsTop.eventually (eventually_ge_atTop (max Y₀ 100))] with
      k hsk
  intro n hhalf hnear
  let s := Nat.sqrt k
  let u := ReciprocalPrimeSelection.sourcePrimeUpper k
  let H := farSeparation u
  let y := Nat.sqrt n
  let x := Nat.sqrt (n - k)
  have hkn : k ≤ n := hhalf.trans (Nat.div_le_self n 2)
  have h2kn : 2 * k ≤ n := by omega
  have hsy : s ≤ y := Nat.sqrt_le_sqrt hkn
  have hs100 : 100 ≤ s := (le_max_right Y₀ 100).trans hsk
  have hY₀y : Y₀ ≤ y := (le_max_left Y₀ 100).trans hsk |>.trans hsy
  have hylog := hY₀ y hY₀y
  have hy100 : 100 ≤ y := hs100.trans hsy
  have hyR : (0 : ℝ) < y := by
    exact_mod_cast (show 0 < y by omega)
  have hGy : 1 ≤ Real.log (y : ℝ) :=
    BoundedGaps.Maynard.one_le_log_natCast (by omega)
  have hus : u ≤ 2 * s := by
    dsimp only [u, ReciprocalPrimeSelection.sourcePrimeUpper]
    omega
  have huy : u ≤ y ^ 2 := by
    calc
      u ≤ 2 * s := hus
      _ ≤ 2 * y := Nat.mul_le_mul_left 2 hsy
      _ ≤ y ^ 2 := by nlinarith
  have hu4 : 4 ≤ u := by
    have hsu : s < u := by
      dsimp only [u, ReciprocalPrimeSelection.sourcePrimeUpper]
      omega
    omega
  have hlogu : Real.log (u : ℝ) ≤ 2 * Real.log (y : ℝ) := by
    have huR : (0 : ℝ) < u := by positivity
    have huyR : (u : ℝ) ≤ (y : ℝ) ^ 2 := by exact_mod_cast huy
    have ht := Real.log_le_log huR huyR
    rw [Real.log_pow] at ht
    norm_num at ht ⊢
    exact ht
  have hH : (H : ℝ) ≤ 512 * Real.log (y : ℝ) ^ 8 := by
    have hcut := logPowerCutoff_le_two_log_pow (e := 8) hu4
    dsimp only [H, farSeparation] at *
    have hpow : Real.log (u : ℝ) ^ 8 ≤
        (2 * Real.log (y : ℝ)) ^ 8 := by gcongr
    calc
      (logPowerCutoff 8 u : ℝ) ≤ 2 * Real.log (u : ℝ) ^ 8 := hcut
      _ ≤ 2 * (2 * Real.log (y : ℝ)) ^ 8 := by gcongr
      _ = 512 * Real.log (y : ℝ) ^ 8 := by ring
  have hHsq : (H : ℝ) ^ 2 ≤
      262144 * Real.log (y : ℝ) ^ 16 := by
    have hH0 : (0 : ℝ) ≤ H := by positivity
    calc
      (H : ℝ) ^ 2 ≤ (512 * Real.log (y : ℝ) ^ 8) ^ 2 := by gcongr
      _ = 262144 * Real.log (y : ℝ) ^ 16 := by ring
  have hsSq : s ^ 2 ≤ k := by
    simpa only [s, pow_two] using Nat.sqrt_le k
  have huSq : u ^ 2 ≤ 4 * k := by
    calc
      u ^ 2 ≤ (2 * s) ^ 2 := by gcongr
      _ = 4 * s ^ 2 := by ring
      _ ≤ 4 * k := Nat.mul_le_mul_left 4 hsSq
  have hySq : y ^ 2 ≤ n := by
    simpa only [y, pow_two] using Nat.sqrt_le n
  have hy2k : (y : ℝ) ^ 2 <
      1048576 * Real.log (y : ℝ) ^ 16 * k := by
    have huSqR : (u : ℝ) ^ 2 ≤ 4 * k := by exact_mod_cast huSq
    have hySqR : (y : ℝ) ^ 2 ≤ n := by exact_mod_cast hySq
    calc
      (y : ℝ) ^ 2 ≤ n := hySqR
      _ < (H : ℝ) ^ 2 * (u : ℝ) ^ 2 := hnear
      _ ≤ (262144 * Real.log (y : ℝ) ^ 16) * (4 * k) := by gcongr
      _ = 1048576 * Real.log (y : ℝ) ^ 16 * k := by ring
  have hHsmall : (16 : ℝ) * (H : ℝ) ^ 2 ≤ (y : ℝ) := by
    calc
      16 * (H : ℝ) ^ 2 ≤
          4194304 * Real.log (y : ℝ) ^ 16 := by
        nlinarith [hHsq]
      _ ≤ (y : ℝ) := hylog
  have hkLarge : 4 * y < k := by
    have hHpos : (0 : ℝ) < H := by
      exact_mod_cast logPowerCutoff_pos 8 u
    have hnear' : (y : ℝ) ^ 2 < 4 * (H : ℝ) ^ 2 * k := by
      have huSqR : (u : ℝ) ^ 2 ≤ 4 * k := by exact_mod_cast huSq
      have hySqR : (y : ℝ) ^ 2 ≤ n := by exact_mod_cast hySq
      calc
        (y : ℝ) ^ 2 ≤ n := hySqR
        _ < (H : ℝ) ^ 2 * (u : ℝ) ^ 2 := hnear
        _ ≤ (H : ℝ) ^ 2 * (4 * k) := by gcongr
        _ = 4 * (H : ℝ) ^ 2 * k := by ring
    have : (4 : ℝ) * y < k := by nlinarith
    exact_mod_cast this
  have hxn : x ≤ y := Nat.sqrt_le_sqrt (Nat.sub_le n k)
  have hxy : x < y := by
    apply lt_of_le_of_ne hxn
    intro hEq
    have hEq' : x = y := hEq
    have hxSq : x ^ 2 ≤ n - k := by
      simpa only [x, pow_two] using Nat.sqrt_le (n - k)
    have hnUpper : n < (y + 1) ^ 2 := by
      simpa only [y, pow_two] using Nat.lt_succ_sqrt n
    have hkx : k + x ^ 2 ≤ n := by omega
    nlinarith
  have hxSq : x ^ 2 ≤ n - k := by
    simpa only [x, pow_two] using Nat.sqrt_le (n - k)
  have hnUpper : n ≤ y ^ 2 + 2 * y := by
    have hlt : n < (y + 1) ^ 2 := by
      simpa only [y, pow_two] using Nat.lt_succ_sqrt n
    nlinarith
  have hkx : k + x ^ 2 ≤ n := by omega
  have hkGap : (k : ℝ) ≤ 4 * (y : ℝ) * ((y : ℝ) - x) := by
    have hxyOneNat : 1 ≤ y - x := by omega
    have hxyOne : (1 : ℝ) ≤ (y : ℝ) - x := by exact_mod_cast hxyOneNat
    have hsumNat : x + y ≤ 2 * y := by omega
    have hsum : (x : ℝ) + y ≤ 2 * y := by exact_mod_cast hsumNat
    have hsum' : (y : ℝ) + x ≤ 2 * y := by linarith
    have hgap0 : (0 : ℝ) ≤ (y : ℝ) - x := by
      have hxnR : (x : ℝ) ≤ y := by exact_mod_cast hxn
      exact sub_nonneg.mpr hxnR
    have hbase : (k : ℝ) ≤ (y : ℝ) ^ 2 + 2 * y - (x : ℝ) ^ 2 := by
      have hbaseNat : k + x ^ 2 ≤ y ^ 2 + 2 * y := hkx.trans hnUpper
      have hbaseR : (k : ℝ) + x ^ 2 ≤ y ^ 2 + 2 * y := by
        exact_mod_cast hbaseNat
      nlinarith
    calc
      (k : ℝ) ≤ (y : ℝ) ^ 2 + 2 * y - (x : ℝ) ^ 2 := hbase
      _ = ((y : ℝ) - x) * (y + x) + 2 * y := by ring
      _ ≤ ((y : ℝ) - x) * (2 * y) + 2 * y := by
        simpa only [add_comm] using
          add_le_add_right (mul_le_mul_of_nonneg_left hsum' hgap0) (2 * y)
      _ ≤ ((y : ℝ) - x) * (2 * y) + 2 * y * ((y : ℝ) - x) := by
        have htwoY : (0 : ℝ) ≤ 2 * y := by positivity
        have hmul := mul_le_mul_of_nonneg_left hxyOne htwoY
        nlinarith
      _ = 4 * (y : ℝ) * ((y : ℝ) - x) := by ring
  have hgapStrong : (y : ℝ) /
      (4194304 * Real.log (y : ℝ) ^ 16) < (y : ℝ) - x := by
    have hlogpos : 0 < Real.log (y : ℝ) ^ 16 := pow_pos (by positivity) 16
    have hden : 0 < 4194304 * Real.log (y : ℝ) ^ 16 := by positivity
    rw [div_lt_iff₀ hden]
    have := lt_of_lt_of_le hy2k (mul_le_mul_of_nonneg_left hkGap (by positivity))
    nlinarith
  dsimp only [y, x] at hgapStrong ⊢
  exact le_of_lt <| calc
      (Nat.sqrt n : ℝ) /
            (10000000 * Real.log (Nat.sqrt n : ℝ) ^ 16) ≤
          (Nat.sqrt n : ℝ) /
            (4194304 * Real.log (Nat.sqrt n : ℝ) ^ 16) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        gcongr
        norm_num
      _ < (Nat.sqrt n : ℝ) - Nat.sqrt (n - k) := hgapStrong

theorem eventually_near_primeLogMass_lower_uniform :
    ∀ᶠ k : ℕ in atTop, ∀ n : ℕ,
      k ≤ n / 2 →
      (n : ℝ) <
        (farSeparation (ReciprocalPrimeSelection.sourcePrimeUpper k) : ℝ) ^ 2 *
          (ReciprocalPrimeSelection.sourcePrimeUpper k : ℝ) ^ 2 →
      (Nat.sqrt n : ℝ) /
          (100000000 * Real.log (Nat.sqrt n : ℝ) ^ 16) ≤
        primeIntervalLogMass (Nat.sqrt (n - k)) (Nat.sqrt n) := by
  have hsTop : Tendsto (fun k : ℕ ↦ Nat.sqrt k) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro B
    exact ⟨B ^ 2, fun k hk ↦ Nat.le_sqrt'.mpr hk⟩
  have hgap := eventually_near_sqrt_gap_lower
  rcases eventually_near_primeLogMass_lower.exists_forall_of_atTop with
    ⟨Y, hY⟩
  filter_upwards [hgap,
    hsTop.eventually (eventually_ge_atTop (max Y 100))] with k hgap hsk
  intro n hhalf hnear
  let y := Nat.sqrt n
  let x := Nat.sqrt (n - k)
  have h2kn : 2 * k ≤ n := by
    simpa only [Nat.mul_comm] using
      (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mp hhalf
  have hkn : k ≤ n := by omega
  have hkSub : k ≤ n - k := by omega
  have hyLarge : max Y 100 ≤ y :=
    hsk.trans (Nat.sqrt_le_sqrt hkn)
  have hyY : Y ≤ y := (le_max_left _ _).trans hyLarge
  have hsx : Nat.sqrt k ≤ x := Nat.sqrt_le_sqrt hkSub
  have hx100 : 100 ≤ x := (le_max_right Y 100).trans hsk |>.trans hsx
  have hgapD := hgap n hhalf hnear
  have hyR : (0 : ℝ) < y := by
    exact_mod_cast (show 0 < y by omega)
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hxy : x < y := by
    dsimp only [x, y] at hgapD ⊢
    exact_mod_cast (show (Nat.sqrt (n - k) : ℝ) < Nat.sqrt n by
      have : 0 < (Nat.sqrt n : ℝ) /
          (10000000 * Real.log (Nat.sqrt n : ℝ) ^ 16) := by
        have hyR' : (0 : ℝ) < Nat.sqrt n := by simpa only [y] using hyR
        have hlog' : 0 < Real.log (Nat.sqrt n : ℝ) := by
          simpa only [y] using hlog
        exact div_pos hyR' (by positivity)
      nlinarith)
  have hy2x : y ≤ 2 * x := by
    by_contra hnot
    have hlarge : 2 * x < y := Nat.lt_of_not_ge hnot
    have hySq : y ^ 2 ≤ n := by
      simpa only [y, pow_two] using Nat.sqrt_le n
    have hxUpper : n - k < (x + 1) ^ 2 := by
      simpa only [x, pow_two] using Nat.lt_succ_sqrt (n - k)
    have hnSub : n ≤ 2 * (n - k) := by omega
    nlinarith
  exact hY y hyY x hxy hy2x hgapD

lemma farSeparation_mono {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    farSeparation a ≤ farSeparation b := by
  unfold farSeparation logPowerCutoff
  gcongr

/-! ## The moving near-`sqrt n` window -/

structure NearPhaseDatum where
  k : ℕ
  n : ℕ
  X : ℕ
  hhalf : k ≤ n / 2
  hnear : (n : ℝ) <
    (farSeparation (ReciprocalPrimeSelection.sourcePrimeUpper k) : ℝ) ^ 2 *
      (ReciprocalPrimeSelection.sourcePrimeUpper k : ℝ) ^ 2
  hkX : k ≤ X
  hXn : X ≤ n

def nearPhaseFilter : Filter NearPhaseDatum :=
  Filter.comap NearPhaseDatum.k atTop

lemma tendsto_nearDatum_k_atTop :
    Tendsto NearPhaseDatum.k nearPhaseFilter atTop := by
  rw [tendsto_def]
  exact Filter.map_comap_le

lemma tendsto_nearDatum_sqrt_n_atTop :
    Tendsto (fun d : NearPhaseDatum ↦ Nat.sqrt d.n) nearPhaseFilter atTop := by
  rw [tendsto_atTop]
  intro B
  have hk := tendsto_nearDatum_k_atTop.eventually
    (eventually_ge_atTop (B ^ 2))
  filter_upwards [hk] with d hd
  apply Nat.le_sqrt'.mpr
  exact hd.trans (d.hhalf.trans (Nat.div_le_self d.n 2))

theorem tendsto_near_normalized_centered :
    Tendsto (fun d : NearPhaseDatum ↦
      (primeIntervalLogMass (Nat.sqrt (d.n - d.k)) (Nat.sqrt d.n))⁻¹ *
        centeredReciprocalPrimeSum (Nat.sqrt (d.n - d.k))
          (Nat.sqrt d.n) d.X) nearPhaseFilter (nhds 0) := by
  let a : NearPhaseDatum → ℕ := fun d ↦ Nat.sqrt (d.n - d.k)
  let b : NearPhaseDatum → ℕ := fun d ↦ Nat.sqrt d.n
  let X : NearPhaseDatum → ℕ := fun d ↦ d.X
  have hkTop : Tendsto (fun d : NearPhaseDatum ↦ d.k)
      nearPhaseFilter atTop := tendsto_nearDatum_k_atTop
  have hbTop : Tendsto b nearPhaseFilter atTop :=
    tendsto_nearDatum_sqrt_n_atTop
  have hgeom : ∀ᶠ d in nearPhaseFilter,
      a d < b d ∧ b d ≤ 2 * a d ∧ 0 < X d ∧
      (b d : ℝ) ^ 2 ≤
        4 * (farSeparation (b d) : ℝ) ^ 2 * X d ∧
      X d ≤ b d ^ 15 ∧
      (b d : ℝ) /
          (100000000 * Real.log (b d : ℝ) ^ 16) ≤
        primeIntervalLogMass (a d) (b d) := by
    have hgap := hkTop.eventually eventually_near_sqrt_gap_lower
    have hmass := hbTop.eventually eventually_near_primeLogMass_lower
    have hsTop : Tendsto (fun d : NearPhaseDatum ↦ Nat.sqrt d.k)
        nearPhaseFilter atTop := by
      exact (show Tendsto (fun k : ℕ ↦ Nat.sqrt k) atTop atTop by
        rw [tendsto_atTop_atTop]
        intro B
        exact ⟨B ^ 2, fun k hk ↦ Nat.le_sqrt'.mpr hk⟩).comp hkTop
    filter_upwards [hgap, hmass,
      hsTop.eventually (eventually_ge_atTop 100)] with d hgap hmass hs100
    let s := Nat.sqrt d.k
    let u := ReciprocalPrimeSelection.sourcePrimeUpper d.k
    let y := Nat.sqrt d.n
    let x := Nat.sqrt (d.n - d.k)
    let H := farSeparation u
    have hkn : d.k ≤ d.n := d.hhalf.trans (Nat.div_le_self d.n 2)
    have h2kn : 2 * d.k ≤ d.n := by
      simpa only [Nat.mul_comm] using
        (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mp d.hhalf
    have hkSub : d.k ≤ d.n - d.k := by omega
    have hsSq : s ^ 2 ≤ d.k := by
      simpa only [s, pow_two] using Nat.sqrt_le d.k
    have h9u : 9 * u ≤ 10 * s := by
      dsimp only [u, s, ReciprocalPrimeSelection.sourcePrimeUpper]
      omega
    have huSq : u ^ 2 ≤ 2 * d.k := by nlinarith
    have huy : u ≤ y := by
      apply Nat.le_sqrt'.mpr
      exact huSq.trans h2kn
    have hu1 : 1 ≤ u := by
      dsimp only [u, ReciprocalPrimeSelection.sourcePrimeUpper, s]
      omega
    have hHmono : H ≤ farSeparation y :=
      farSeparation_mono hu1 huy
    have hgapD := hgap d.n d.hhalf d.hnear
    have hy100 : 100 ≤ y := by
      exact hs100.trans (Nat.sqrt_le_sqrt hkn)
    have hyR : (0 : ℝ) < y := by positivity
    have hlogy : 0 < Real.log (y : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < y by omega))
    have hden : 0 < 10000000 * Real.log (y : ℝ) ^ 16 := by positivity
    have hxy : x < y := by
      have hpos : 0 < (y : ℝ) /
          (10000000 * Real.log (y : ℝ) ^ 16) := div_pos hyR hden
      dsimp only [x, y] at hgapD ⊢
      exact_mod_cast (show (Nat.sqrt (d.n - d.k) : ℝ) < Nat.sqrt d.n by
        nlinarith)
    have hsx : s ≤ x := Nat.sqrt_le_sqrt hkSub
    have hx100 : 100 ≤ x := hs100.trans hsx
    have hy2x : y ≤ 2 * x := by
      by_contra hnot
      have hlarge : 2 * x < y := Nat.lt_of_not_ge hnot
      have hySq : y ^ 2 ≤ d.n := by
        simpa only [y, pow_two] using Nat.sqrt_le d.n
      have hxUpper : d.n - d.k < (x + 1) ^ 2 := by
        simpa only [x, pow_two] using Nat.lt_succ_sqrt (d.n - d.k)
      have hnSub : d.n ≤ 2 * (d.n - d.k) := by omega
      nlinarith
    have hySq : y ^ 2 ≤ d.n := by
      simpa only [y, pow_two] using Nat.sqrt_le d.n
    have hrelaxed : (y : ℝ) ^ 2 ≤
        4 * (farSeparation y : ℝ) ^ 2 * d.X := by
      have hySqR : (y : ℝ) ^ 2 ≤ d.n := by exact_mod_cast hySq
      have huSqR : (u : ℝ) ^ 2 ≤ 2 * d.k := by exact_mod_cast huSq
      have hHmonoR : (H : ℝ) ≤ farSeparation y := by exact_mod_cast hHmono
      have hH0 : (0 : ℝ) ≤ H := by positivity
      have hkXR : (d.k : ℝ) ≤ d.X := by exact_mod_cast d.hkX
      exact le_of_lt <| calc
        (y : ℝ) ^ 2 ≤ d.n := hySqR
        _ < (H : ℝ) ^ 2 * (u : ℝ) ^ 2 := d.hnear
        _ ≤ (farSeparation y : ℝ) ^ 2 * (2 * d.k) := by gcongr
        _ < 4 * (farSeparation y : ℝ) ^ 2 * d.X := by
          have hsquare : (0 : ℝ) ≤ (farSeparation y : ℝ) ^ 2 := sq_nonneg _
          have hmul := mul_le_mul_of_nonneg_left hkXR hsquare
          have hkpos : 0 < d.k := by nlinarith [hsSq]
          have hXposR : (0 : ℝ) < d.X := by
            exact_mod_cast (lt_of_lt_of_le hkpos d.hkX)
          have hsepPos : (0 : ℝ) < farSeparation y := by
            exact_mod_cast logPowerCutoff_pos 8 y
          calc
            (farSeparation y : ℝ) ^ 2 * (2 * d.k) =
                2 * (farSeparation y : ℝ) ^ 2 * d.k := by ring
            _ ≤ 2 * (farSeparation y : ℝ) ^ 2 * d.X := by gcongr
            _ < 4 * (farSeparation y : ℝ) ^ 2 * d.X := by
              nlinarith [sq_pos_of_pos hsepPos]
    have hnUpper : d.n < (y + 1) ^ 2 := by
      simpa only [y, pow_two] using Nat.lt_succ_sqrt d.n
    have hyBase : y + 1 ≤ y ^ 2 := by nlinarith
    have hyFour : (y + 1) ^ 2 ≤ y ^ 4 := by
      calc
        (y + 1) ^ 2 ≤ (y ^ 2) ^ 2 := by gcongr
        _ = y ^ 4 := by ring
    have hyPow : y ^ 4 ≤ y ^ 15 := by
      calc
        y ^ 4 = y ^ 4 * 1 := by simp
        _ ≤ y ^ 4 * y ^ 11 :=
          Nat.mul_le_mul_left _ (one_le_pow₀ (by omega : 1 ≤ y))
        _ = y ^ 15 := by ring
    have hXpow : d.X ≤ y ^ 15 :=
      d.hXn.trans hnUpper.le |>.trans (hyFour.trans hyPow)
    have hmassD := hmass x hxy hy2x hgapD
    have hkpos : 0 < d.k := by nlinarith [hsSq]
    exact ⟨hxy, hy2x, lt_of_lt_of_le hkpos d.hkX,
      hrelaxed, hXpow, hmassD⟩
  have h := tendsto_normalizedCenteredPrimeInterval_relaxed a b X
    (C := 100000000) (by norm_num) hbTop hgeom
  simpa only [a, b, X] using h

theorem eventually_near_centered_small :
    ∀ᶠ k : ℕ in atTop, ∀ n X : ℕ,
      k ≤ n / 2 →
      (n : ℝ) <
        (farSeparation (ReciprocalPrimeSelection.sourcePrimeUpper k) : ℝ) ^ 2 *
          (ReciprocalPrimeSelection.sourcePrimeUpper k : ℝ) ^ 2 →
      k ≤ X → X ≤ n →
      |centeredReciprocalPrimeSum (Nat.sqrt (n - k)) (Nat.sqrt n) X| <
        primeIntervalLogMass (Nat.sqrt (n - k)) (Nat.sqrt n) / 1000 := by
  have hnorm : ∀ᶠ d : NearPhaseDatum in nearPhaseFilter,
      |(primeIntervalLogMass (Nat.sqrt (d.n - d.k)) (Nat.sqrt d.n))⁻¹ *
        centeredReciprocalPrimeSum (Nat.sqrt (d.n - d.k))
          (Nat.sqrt d.n) d.X| < 1 / 1000 :=
    tendsto_near_normalized_centered.eventually
      (Metric.ball_mem_nhds 0 (by norm_num : (0 : ℝ) < 1 / 1000)) |>.mono (by
        intro d hd
        simpa only [Real.dist_eq, sub_zero] using hd)
  have hmass : ∀ᶠ d : NearPhaseDatum in nearPhaseFilter,
      0 < primeIntervalLogMass (Nat.sqrt (d.n - d.k)) (Nat.sqrt d.n) := by
    have hbTop := tendsto_nearDatum_sqrt_n_atTop
    have hkTop := tendsto_nearDatum_k_atTop
    have hsTop : Tendsto (fun d : NearPhaseDatum ↦ Nat.sqrt d.k)
        nearPhaseFilter atTop := by
      exact (show Tendsto (fun k : ℕ ↦ Nat.sqrt k) atTop atTop by
        rw [tendsto_atTop_atTop]
        intro B
        exact ⟨B ^ 2, fun k hk ↦ Nat.le_sqrt'.mpr hk⟩).comp hkTop
    have hgap := hkTop.eventually eventually_near_sqrt_gap_lower
    have hlower := hbTop.eventually eventually_near_primeLogMass_lower
    filter_upwards [hgap, hlower,
      hbTop.eventually (eventually_ge_atTop 100),
      hsTop.eventually (eventually_ge_atTop 100)] with d hgap hlower hy hs
    have hgapD := hgap d.n d.hhalf d.hnear
    have hxy : Nat.sqrt (d.n - d.k) < Nat.sqrt d.n := by
      have hyR : (0 : ℝ) < Nat.sqrt d.n := by exact_mod_cast (show 0 < Nat.sqrt d.n by omega)
      have hlog : 0 < Real.log (Nat.sqrt d.n : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < Nat.sqrt d.n by omega))
      have hpos : 0 < (Nat.sqrt d.n : ℝ) /
          (10000000 * Real.log (Nat.sqrt d.n : ℝ) ^ 16) := by
        exact div_pos hyR (by positivity)
      exact_mod_cast (show (Nat.sqrt (d.n - d.k) : ℝ) < Nat.sqrt d.n by
        nlinarith)
    have hyx : Nat.sqrt d.n ≤ 2 * Nat.sqrt (d.n - d.k) := by
      have h2kn : 2 * d.k ≤ d.n := by
        simpa only [Nat.mul_comm] using
          (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mp d.hhalf
      have hkSub : d.k ≤ d.n - d.k := by
        omega
      have hsx := Nat.sqrt_le_sqrt hkSub
      have hx100 : 100 ≤ Nat.sqrt (d.n - d.k) := hs.trans hsx
      by_contra hnot
      have hlarge : 2 * Nat.sqrt (d.n - d.k) < Nat.sqrt d.n :=
        Nat.lt_of_not_ge hnot
      have hySq := Nat.sqrt_le d.n
      have hxUpper := Nat.lt_succ_sqrt (d.n - d.k)
      have hnSub : d.n ≤ 2 * (d.n - d.k) := by omega
      nlinarith
    have hbound := hlower _ hxy hyx hgapD
    have hyR : (0 : ℝ) < Nat.sqrt d.n := by exact_mod_cast (show 0 < Nat.sqrt d.n by omega)
    have hlog : 0 < Real.log (Nat.sqrt d.n : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < Nat.sqrt d.n by omega))
    exact lt_of_lt_of_le (div_pos hyR (by positivity)) hbound
  unfold nearPhaseFilter at hnorm hmass
  rw [Filter.eventually_comap, Filter.eventually_atTop] at hnorm hmass
  rcases hnorm with ⟨K₁, hK₁⟩
  rcases hmass with ⟨K₂, hK₂⟩
  filter_upwards [eventually_ge_atTop (max K₁ K₂)] with k hk
  intro n X hhalf hnear hkX hXn
  let d : NearPhaseDatum := ⟨k, n, X, hhalf, hnear, hkX, hXn⟩
  have hd := hK₁ k (le_trans (le_max_left _ _) hk) d rfl
  have hm := hK₂ k (le_trans (le_max_right _ _) hk) d rfl
  dsimp only [d] at hd hm
  rw [abs_mul, abs_of_pos (inv_pos.mpr hm)] at hd
  rw [inv_mul_lt_iff₀ hm] at hd
  nlinarith

theorem tendsto_source_normalized_centered :
    Tendsto (fun d : SourcePhaseDatum ↦
      (ReciprocalPrimeSelection.sourcePrimeLogMass d.k)⁻¹ *
        centeredReciprocalPrimeSum (Nat.sqrt d.k)
          (ReciprocalPrimeSelection.sourcePrimeUpper d.k) d.X)
      sourcePhaseFilter (nhds 0) := by
  let a : SourcePhaseDatum → ℕ := fun d ↦ Nat.sqrt d.k
  let b : SourcePhaseDatum → ℕ := fun d ↦
    ReciprocalPrimeSelection.sourcePrimeUpper d.k
  let X : SourcePhaseDatum → ℕ := fun d ↦ d.X
  have hkTop : Tendsto (fun d : SourcePhaseDatum ↦ d.k)
      sourcePhaseFilter atTop := tendsto_sourceDatum_k_atTop
  have hbTop : Tendsto b sourcePhaseFilter atTop :=
    ReciprocalPrimeSelection.tendsto_sourcePrimeUpper_atTop.comp hkTop
  have hgeom : ∀ᶠ d in sourcePhaseFilter,
      a d < b d ∧ b d ≤ 2 * a d ∧ 0 < X d ∧
      (b d : ℝ) ^ 2 ≤ 4 * X d ∧ X d ≤ b d ^ 15 ∧
      (b d : ℝ) / 40 ≤ primeIntervalLogMass (a d) (b d) := by
    have hmass := hkTop.eventually
      ReciprocalPrimeSelection.eventually_sourcePrimeLogMass_lower
    filter_upwards [hmass, hkTop.eventually (eventually_ge_atTop 8100)] with
      d hmass hk
    have hs : 90 ≤ Nat.sqrt d.k := Nat.le_sqrt'.mpr hk
    have hab : Nat.sqrt d.k <
        ReciprocalPrimeSelection.sourcePrimeUpper d.k := by
      unfold ReciprocalPrimeSelection.sourcePrimeUpper
      omega
    have hba : ReciprocalPrimeSelection.sourcePrimeUpper d.k ≤
        2 * Nat.sqrt d.k := by
      unfold ReciprocalPrimeSelection.sourcePrimeUpper
      omega
    have hkSq : Nat.sqrt d.k ^ 2 ≤ d.k := by
      simpa only [pow_two] using Nat.sqrt_le d.k
    have hbSq : ReciprocalPrimeSelection.sourcePrimeUpper d.k ^ 2 ≤
        4 * d.k := by
      calc
        ReciprocalPrimeSelection.sourcePrimeUpper d.k ^ 2 ≤
            (2 * Nat.sqrt d.k) ^ 2 := by gcongr
        _ = 4 * Nat.sqrt d.k ^ 2 := by ring
        _ ≤ 4 * d.k := Nat.mul_le_mul_left 4 hkSq
    have hmass' : (ReciprocalPrimeSelection.sourcePrimeUpper d.k : ℝ) / 40 ≤
        ReciprocalPrimeSelection.sourcePrimeLogMass d.k := by
      have hbaR : (ReciprocalPrimeSelection.sourcePrimeUpper d.k : ℝ) ≤
          2 * Nat.sqrt d.k := by exact_mod_cast hba
      nlinarith
    exact ⟨hab, hba, (lt_of_lt_of_le (by omega : 0 < d.k) d.hkX), by
      exact_mod_cast hbSq.trans (Nat.mul_le_mul_left 4 d.hkX), d.hX, by
        simpa only [a, b, source_primeIntervalLogMass] using hmass'⟩
  have h := tendsto_normalizedCenteredPrimeInterval_central a b X
    (C := 40) (by norm_num) hbTop hgeom
  simpa only [a, b, X, source_primeIntervalLogMass] using h

theorem eventually_source_centered_small :
    ∀ᶠ k : ℕ in atTop, ∀ X : ℕ,
      k ≤ X → X ≤ ReciprocalPrimeSelection.sourcePrimeUpper k ^ 15 →
      |centeredReciprocalPrimeSum (Nat.sqrt k)
          (ReciprocalPrimeSelection.sourcePrimeUpper k) X| <
        ReciprocalPrimeSelection.sourcePrimeLogMass k / 1000 := by
  have hnorm : ∀ᶠ d : SourcePhaseDatum in sourcePhaseFilter,
      |(ReciprocalPrimeSelection.sourcePrimeLogMass d.k)⁻¹ *
        centeredReciprocalPrimeSum (Nat.sqrt d.k)
          (ReciprocalPrimeSelection.sourcePrimeUpper d.k) d.X| < 1 / 1000 :=
    tendsto_source_normalized_centered.eventually
      (Metric.ball_mem_nhds 0 (by norm_num : (0 : ℝ) < 1 / 1000)) |>.mono (by
        intro d hd
        simpa only [Real.dist_eq, sub_zero] using hd)
  have hmass : ∀ᶠ k : ℕ in atTop,
      0 < ReciprocalPrimeSelection.sourcePrimeLogMass k := by
    filter_upwards [ReciprocalPrimeSelection.eventually_sourcePrimeLogMass_lower,
      eventually_gt_atTop 0] with k hk hsk
    exact lt_of_lt_of_le
      (div_pos (by exact_mod_cast (Nat.sqrt_pos.2 hsk)) (by norm_num)) hk
  unfold sourcePhaseFilter at hnorm
  rw [Filter.eventually_comap, Filter.eventually_atTop] at hnorm
  rcases hnorm with ⟨K, hK⟩
  filter_upwards [hmass, eventually_ge_atTop K] with k hmassK hk
  intro X hkX hX
  let d : SourcePhaseDatum := ⟨k, X, hkX, hX⟩
  have hd := hK k hk d rfl
  dsimp only [d] at hd
  rw [abs_mul, abs_of_pos (inv_pos.mpr hmassK)] at hd
  rw [inv_mul_lt_iff₀ hmassK] at hd
  nlinarith

lemma norm_shiftedInverseSquarePrimeMode (h n k : ℕ) :
    ‖InverseSquareExceptionalArc.shiftedInverseSquarePrimeMode h n k‖ =
      ‖primeWeightedInterval
        (InverseSquareCorrelation.inverseSquareWeight (((h * n : ℕ) : ℝ)))
        (Nat.sqrt k) (ReciprocalPrimeSelection.sourcePrimeUpper k)‖ := by
  unfold InverseSquareExceptionalArc.shiftedInverseSquarePrimeMode
    InverseSquareExceptionalArc.inverseSquarePrimeMode
  rw [norm_mul, norm_e, one_mul]

theorem eventually_exceptionalPrimeLogMass_lt :
    ∀ᶠ k : ℕ in atTop, ∀ n : ℕ,
      k ≤ n →
      (farSeparation (ReciprocalPrimeSelection.sourcePrimeUpper k) : ℝ) ^ 2 *
          (ReciprocalPrimeSelection.sourcePrimeUpper k : ℝ) ^ 2 ≤ n →
      n ≤ ReciprocalPrimeSelection.sourcePrimeUpper k ^ 15 →
      InverseSquareExceptionalArc.exceptionalPrimeLogMass n k <
        (43 / 100 : ℝ) * ReciprocalPrimeSelection.sourcePrimeLogMass k := by
  have hfarSmall : ∀ᶠ y : ℕ in atTop,
      HighIndexChebyshev.farPrimeMajorant y / (y : ℝ) < 1 / 100000 :=
    HighIndexChebyshev.tendsto_farPrimeMajorant_div_zero.eventually
      (Iio_mem_nhds (by norm_num))
  have hsourceTop := ReciprocalPrimeSelection.tendsto_sourcePrimeUpper_atTop
  have hsmallK := hsourceTop.eventually hfarSmall
  have hfarBound := hsourceTop.eventually
    HighIndexChebyshev.eventually_farPrime_bound
  filter_upwards [hsmallK, hfarBound,
    ReciprocalPrimeSelection.eventually_sourcePrimeLogMass_lower,
    hsourceTop.eventually (eventually_ge_atTop 90),
    eventually_ge_atTop 8100] with
      k hsmall hbound hmass hy hklarge
  intro n hkn hfar hn15
  let y := ReciprocalPrimeSelection.sourcePrimeUpper k
  let x := Nat.sqrt k
  let M := HighIndexChebyshev.farPrimeMajorant y
  let W := ReciprocalPrimeSelection.sourcePrimeLogMass k
  have hs : 2 ≤ x := by
    dsimp only [x]
    have hs90 : 90 ≤ Nat.sqrt k := Nat.le_sqrt'.mpr hklarge
    omega
  have hxy : x < y := by
    dsimp only [x, y, ReciprocalPrimeSelection.sourcePrimeUpper]
    have hs9 : 9 ≤ Nat.sqrt k :=
      (show 9 ≤ 90 by omega).trans (Nat.le_sqrt'.mpr hklarge)
    omega
  have hyx : y ≤ 2 * x := by
    dsimp only [x, y, ReciprocalPrimeSelection.sourcePrimeUpper]
    omega
  have hkSq : x ^ 2 ≤ k := by
    simpa only [x, pow_two] using Nat.sqrt_le k
  have hySq : y ^ 2 ≤ 4 * k := by
    have hyx' : y ≤ 2 * x := hyx
    calc
      y ^ 2 ≤ (2 * x) ^ 2 := by gcongr
      _ = 4 * x ^ 2 := by ring
      _ ≤ 4 * k := Nat.mul_le_mul_left 4 hkSq
  have hypos : 0 < y := by omega
  have hMsmall : M < W / 2500 := by
    have hyR : (0 : ℝ) < y := by exact_mod_cast hypos
    have hmassY : (y : ℝ) / 40 ≤ W := by
      have hyxR : (y : ℝ) ≤ 2 * x := by exact_mod_cast hyx
      dsimp only [W]
      dsimp only [x] at hyxR
      nlinarith
    have hM : M < (y : ℝ) / 100000 := by
      dsimp only [M, y] at hsmall ⊢
      rw [div_lt_iff₀ hyR] at hsmall
      nlinarith
    nlinarith
  have hmode (h : ℕ) (hh : 1 ≤ h) (hhy : h ≤ y) :
      ‖InverseSquareExceptionalArc.shiftedInverseSquarePrimeMode h n k‖ ≤ M := by
    rw [norm_shiftedInverseSquarePrimeMode]
    have hfreq : (0 : ℝ) < ((h * n : ℕ) : ℝ) := by
      have hkpos : 0 < k := by omega
      have hnpos : 0 < n := lt_of_lt_of_le hkpos hkn
      positivity
    have hlo : (y : ℝ) ^ 2 ≤ 4 * ((h * n : ℕ) : ℝ) := by
      have hnat : y ^ 2 ≤ 4 * (h * n) := by
        calc
          y ^ 2 ≤ 4 * k := hySq
          _ ≤ 4 * (h * n) := by gcongr; nlinarith
      exact_mod_cast hnat
    have hhi : h * n ≤ y ^ 16 := by
      calc
        h * n ≤ y * y ^ 15 := Nat.mul_le_mul hhy hn15
        _ = y ^ 16 := by ring
    have hratio : (farSeparation y : ℝ) ^ 2 * (y : ℝ) ^ 2 ≤
        ((h * n : ℕ) : ℝ) := by
      have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
      push_cast
      nlinarith
    exact hbound hxy hyx hfreq hlo (by exact_mod_cast hhi) hratio
  have hm1 := hmode 1 (by omega) (by omega)
  have hm2 := hmode 2 (by omega) (by omega)
  have hm3 := hmode 3 (by omega) (by omega)
  have hm4 := hmode 4 (by omega) (by omega)
  have hre1 := abs_le.mp ((Complex.abs_re_le_norm _).trans hm1)
  have hre2 := abs_le.mp ((Complex.abs_re_le_norm _).trans hm2)
  have hre3 := abs_le.mp ((Complex.abs_re_le_norm _).trans hm3)
  have hre4 := abs_le.mp ((Complex.abs_re_le_norm _).trans hm4)
  refine (InverseSquareExceptionalArc.exceptionalPrimeLogMass_le_majorantSum n k).trans_lt ?_
  rw [InverseSquareExceptionalArc.exceptionalArcMajorantSum_eq_modes]
  dsimp only [M, W] at hMsmall hre1 hre2 hre3 hre4 ⊢
  unfold InverseSquareExceptionalArc.exceptionalArcMean
  nlinarith

end

end HighIndexCentered
end Erdos378
