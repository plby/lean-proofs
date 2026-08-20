import ErdosProblems.Erdos823.AffineSieve
import BoundedGaps.Maynard.ConcreteS2RestrictedShiftCoefficient
import BoundedGaps.Maynard.ConcretePrimeCountPNTInterval
import BoundedGaps.Maynard.ConcreteRadiusLogAsymptotics
import BoundedGaps.Maynard.ConcreteShiftedPrimeEndpointLimit
import BoundedGaps.Maynard.ConcreteS2MainNumeratorLimit
import BoundedGaps.Maynard.ImprovedGPY.S2TauDistribution
import BoundedGaps.Maynard.ImprovedGPY.S2TauShiftedAggregation
import BoundedGaps.Maynard.ConcreteS2TauErrorLimit
import BoundedGaps.PrimeNumberTheorem.Proof.MainTheorem

/-!
# The affine second moment

This file transports the prime-weighted part of the concrete Maynard sieve
from translated primes to the primitive affine forms `c i * n - 1`.
-/

namespace Erdos823

open Filter Finset
open scoped BigOperators

noncomputable section

namespace AffineSieve

local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem affinePrimeProgressionCount_eq_primeVariableProgressionCount
    {a N q r : ℕ} (ha : 0 < a) (hN : 0 < N) (hq : 0 < q) :
    affinePrimeProgressionCount a N q r =
      BoundedGaps.Maynard.primeVariableProgressionCount
        (a * N - 1) (a * (2 * N) - 1) (a * q) (a * r + a * q - 1) := by
  unfold affinePrimeProgressionCount
    BoundedGaps.Maynard.primeVariableProgressionCount
  apply Finset.card_bij (fun n _ ↦ a * n - 1)
  · intro n hn
    obtain ⟨hnrange, hnmod, hnprime⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnlower, hnupper⟩ := Finset.mem_Ico.mp hnrange
    have hnpos : 0 < n := hN.trans_le hnlower
    have hmul_lower : a * N ≤ a * n := Nat.mul_le_mul_left a hnlower
    have hmul_upper : a * n < a * (2 * N) :=
      (Nat.mul_lt_mul_left ha).2 hnupper
    have hleft : 1 ≤ a * n := Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero ha.ne' hnpos.ne')
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ico.mpr ?_, hnprime, ?_⟩
    · exact ⟨Nat.sub_le_sub_right hmul_lower 1,
        Nat.sub_lt_sub_right hleft hmul_upper⟩
    · have hmul : a * n ≡ a * r [MOD a * q] := hnmod.mul_left' a
      have hshift : a * r ≡ a * r + a * q [MOD a * q] := by
        simpa [add_comm, mul_comm] using
          (Nat.ModEq.modulus_mul_add (m := a * q) (a := 1)
            (b := a * r)).symm
      have hright : 1 ≤ a * r + a * q := by
        have haq : 0 < a * q := mul_pos ha hq
        omega
      exact Nat.ModEq.sub_right hleft hright (hmul.trans hshift)
  · intro n₁ hn₁ n₂ hn₂ heq
    have hn₁pos : 0 < n₁ :=
      hN.trans_le (Finset.mem_Ico.mp (Finset.mem_filter.mp hn₁).1).1
    have hn₂pos : 0 < n₂ :=
      hN.trans_le (Finset.mem_Ico.mp (Finset.mem_filter.mp hn₂).1).1
    have hprod : a * n₁ = a * n₂ := by
      have h₁ : 1 ≤ a * n₁ := Nat.one_le_iff_ne_zero.mpr
        (mul_ne_zero ha.ne' hn₁pos.ne')
      have h₂ : 1 ≤ a * n₂ := Nat.one_le_iff_ne_zero.mpr
        (mul_ne_zero ha.ne' hn₂pos.ne')
      have hadd := congrArg (fun x : ℕ ↦ x + 1) heq
      simpa [Nat.sub_add_cancel h₁, Nat.sub_add_cancel h₂] using hadd
    exact Nat.eq_of_mul_eq_mul_left ha hprod
  · intro m hm
    obtain ⟨hmrange, hmprime, hmmod⟩ := Finset.mem_filter.mp hm
    obtain ⟨hmlower, hmupper⟩ := Finset.mem_Ico.mp hmrange
    have haq : 0 < a * q := mul_pos ha hq
    have hrhs : 1 ≤ a * r + a * q := by omega
    have hplus : m + 1 ≡ a * (r + q) [MOD a * q] := by
      have := hmmod.add_right 1
      simpa [Nat.sub_add_cancel hrhs, mul_add] using this
    have hdiv : a ∣ m + 1 := by
      rw [← Nat.modEq_zero_iff_dvd]
      have hmoda := hplus.of_dvd (dvd_mul_right a q)
      exact hmoda.trans ((dvd_mul_right a (r + q)).modEq_zero_nat)
    let n := (m + 1) / a
    have hmuln : a * n = m + 1 := by
      dsimp [n]
      exact Nat.mul_div_cancel' hdiv
    have hnrange : n ∈ Finset.Ico N (2 * N) := by
      apply Finset.mem_Ico.mpr
      have haN : 1 ≤ a * N := Nat.one_le_iff_ne_zero.mpr
        (mul_ne_zero ha.ne' hN.ne')
      have ha2N : 1 ≤ a * (2 * N) := Nat.one_le_iff_ne_zero.mpr
        (mul_ne_zero ha.ne' (by omega))
      have hl : a * N ≤ a * n := by omega
      have hu : a * n < a * (2 * N) := by omega
      exact ⟨Nat.le_of_mul_le_mul_left hl ha,
        Nat.lt_of_mul_lt_mul_left hu⟩
    have hnmod : n ≡ r [MOD q] := by
      have hcancel : n ≡ r + q [MOD q] := by
        apply Nat.ModEq.mul_left_cancel' ha.ne'
        simpa [hmuln, mul_add] using hplus
      exact hcancel.trans (by
        simpa [add_comm, mul_comm] using
          (Nat.ModEq.modulus_mul_add (m := q) (a := 1) (b := r)))
    refine ⟨n, Finset.mem_filter.mpr ⟨hnrange, hnmod, ?_⟩, ?_⟩
    · simpa [hmuln] using hmprime
    · omega

theorem affinePrimeProgressionError_le_global_sum
    {a N q r : ℕ} (ha : 0 < a) (hN : 1 < N) (hq : 0 < q) :
    |affinePrimeProgressionError a N q r| ≤
      BoundedGaps.Maynard.progressionDiscrepancy (a * (2 * N) - 2)
          (a * q) (a * r + a * q - 1) +
        BoundedGaps.Maynard.progressionDiscrepancy (a * N - 2)
          (a * q) (a * r + a * q - 1) := by
  unfold affinePrimeProgressionError affinePrimeProgressionMainTerm
    affinePrimeIntervalCount
  rw [affinePrimeProgressionCount_eq_primeVariableProgressionCount ha (by omega) hq]
  exact BoundedGaps.Maynard.primeVariableProgressionCount_intervalDiscrepancy_le_global_sum
    (by
      have : 1 < a * N := lt_of_lt_of_le hN (Nat.le_mul_of_pos_left N ha)
      omega)
    (by
      have := Nat.mul_le_mul_left a (show N ≤ 2 * N by omega)
      omega)

/-! ## Exact prime-weighted pair expansion -/

def affinePrimeWeightedPairInnerSum
    (c : BoundedGaps.engelsmaTuple → ℕ) (W N : ℕ)
    (coeff : (BoundedGaps.engelsmaTuple → ℕ) → ℝ)
    (d e : BoundedGaps.engelsmaTuple → ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico N (2 * N),
    ∑ i : BoundedGaps.engelsmaTuple,
      if n ≡ 0 [MOD W] ∧ divisorTuplePairCondition c n d e ∧
          (c i * n - 1).Prime
      then coeff d * coeff e else 0

def affineCompatiblePrimeWeightedPairSum
    (c : BoundedGaps.engelsmaTuple → ℕ)
    (D : Finset (BoundedGaps.engelsmaTuple → ℕ)) (W N : ℕ)
    (coeff : (BoundedGaps.engelsmaTuple → ℕ) → ℝ) : ℝ :=
  ∑ d ∈ D,
    ∑ e ∈ D.filter (fun e ↦
      BoundedGaps.Maynard.IsCrossCoordinateCoprime
        BoundedGaps.engelsmaTuple d e),
      affinePrimeWeightedPairInnerSum c W N coeff d e

theorem primeCount_eq_prime_indicator_sum
    (c : BoundedGaps.engelsmaTuple → ℕ) (n : ℕ) :
    (primeCount c n : ℝ) =
      ∑ i : BoundedGaps.engelsmaTuple,
        if (c i * n - 1).Prime then 1 else 0 := by
  classical
  unfold primeCount
  rw [Finset.natCast_card_filter]

theorem primeWeightedSum_preSieved_eq_pairPrimeIndicator
    (c : BoundedGaps.engelsmaTuple → ℕ)
    (D : Finset (BoundedGaps.engelsmaTuple → ℕ))
    (coeff : (BoundedGaps.engelsmaTuple → ℕ) → ℝ) (W N : ℕ) :
    primeWeightedSum c N (preSievedWeight c D coeff W) =
      ∑ d ∈ D, ∑ e ∈ D,
        affinePrimeWeightedPairInnerSum c W N coeff d e := by
  classical
  unfold primeWeightedSum
  simp_rw [primeCount_eq_prime_indicator_sum]
  simp_rw [preSievedWeight_eq_pair_indicator]
  unfold affinePrimeWeightedPairInnerSum
  simp_rw [Finset.mul_sum]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hp : (c i * n - 1).Prime <;>
    by_cases hcond : n ≡ 0 [MOD W] ∧ divisorTuplePairCondition c n d e <;>
      simp [hp, hcond]

theorem primeWeightedSum_preSieved_eq_compatible
    {c : BoundedGaps.engelsmaTuple → ℕ}
    {D : Finset (BoundedGaps.engelsmaTuple → ℕ)}
    {coeff : (BoundedGaps.engelsmaTuple → ℕ) → ℝ} {W N R : ℕ}
    (hD : ∀ d ∈ D,
      BoundedGaps.Maynard.IsMaynardDivisorTuple
        BoundedGaps.engelsmaTuple R W d)
    (hcoverage : CoefficientDifferencesCovered c W) :
    primeWeightedSum c N (preSievedWeight c D coeff W) =
      affineCompatiblePrimeWeightedPairSum c D W N coeff := by
  classical
  rw [primeWeightedSum_preSieved_eq_pairPrimeIndicator]
  unfold affineCompatiblePrimeWeightedPairSum
  apply Finset.sum_congr rfl
  intro d hdmem
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e hemel
  by_cases hcross : BoundedGaps.Maynard.IsCrossCoordinateCoprime
      BoundedGaps.engelsmaTuple d e
  · simp [hcross]
  · have hd := hD d hdmem
    have he := hD e hemel
    have hzero : affinePrimeWeightedPairInnerSum c W N coeff d e = 0 := by
      unfold affinePrimeWeightedPairInnerSum
      apply Finset.sum_eq_zero
      intro n hn
      apply Finset.sum_eq_zero
      intro i hi
      have hfalse : ¬(n ≡ 0 [MOD W] ∧
          divisorTuplePairCondition c n d e) := by
        intro hcond
        exact hcross (isCrossCoordinateCoprime_of_pairCondition
          hd he hcoverage hcond.2)
      have hfalse' : ¬(n ≡ 0 [MOD W] ∧
          divisorTuplePairCondition c n d e ∧ (c i * n - 1).Prime) := by
        intro hcond
        exact hfalse ⟨hcond.1, hcond.2.1⟩
      simp [hfalse']
    simp [hcross, hzero]

theorem affinePrimeWeightedPairInnerSum_eq_progressionCounts
    {c : BoundedGaps.engelsmaTuple → ℕ} {R W N : ℕ}
    {d e : BoundedGaps.engelsmaTuple → ℕ}
    (hcover : CoefficientPrimesCovered c W)
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple
      BoundedGaps.engelsmaTuple R W d)
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple
      BoundedGaps.engelsmaTuple R W e)
    (hcross : BoundedGaps.Maynard.IsCrossCoordinateCoprime
      BoundedGaps.engelsmaTuple d e)
    (coeff : (BoundedGaps.engelsmaTuple → ℕ) → ℝ) :
    affinePrimeWeightedPairInnerSum c W N coeff d e =
      ∑ i : BoundedGaps.engelsmaTuple,
        (affinePrimeProgressionCount (c i) N
          (BoundedGaps.Maynard.divisorPairModulus
            BoundedGaps.engelsmaTuple W d e)
          (pairCrtResidue c R W d e hd he hcross) : ℝ) *
          (coeff d * coeff e) := by
  classical
  unfold affinePrimeWeightedPairInnerSum affinePrimeProgressionCount
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_filter]
  have hpred (n : ℕ) :
      (n ≡ 0 [MOD W] ∧ divisorTuplePairCondition c n d e ∧
          (c i * n - 1).Prime) ↔
        (n ≡ pairCrtResidue c R W d e hd he hcross
            [MOD BoundedGaps.Maynard.divisorPairModulus
              BoundedGaps.engelsmaTuple W d e] ∧
          (c i * n - 1).Prime) := by
    constructor
    · rintro ⟨hres, hpair, hprime⟩
      exact ⟨(modEq_pairCrtResidue_iff hcover hd he hcross n).mpr
        ⟨hres, hpair⟩, hprime⟩
    · rintro ⟨hmod, hprime⟩
      obtain ⟨hres, hpair⟩ :=
        (modEq_pairCrtResidue_iff hcover hd he hcross n).mp hmod
      exact ⟨hres, hpair, hprime⟩
  have hfilter :
      (Finset.Ico N (2 * N)).filter (fun n ↦
        n ≡ 0 [MOD W] ∧ divisorTuplePairCondition c n d e ∧
          (c i * n - 1).Prime) =
      (Finset.Ico N (2 * N)).filter (fun n ↦
        n ≡ pairCrtResidue c R W d e hd he hcross
            [MOD BoundedGaps.Maynard.divisorPairModulus
              BoundedGaps.engelsmaTuple W d e] ∧
          (c i * n - 1).Prime) := by
    ext n
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hn, hp⟩
      exact ⟨hn, (hpred n).mp hp⟩
    · rintro ⟨hn, hp⟩
      exact ⟨hn, (hpred n).mpr hp⟩
  rw [hfilter, Finset.sum_const]
  simp [nsmul_eq_mul]

theorem isMaynard_coordinate_lt_radius
    {R W : ℕ} {d : BoundedGaps.engelsmaTuple → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple
      BoundedGaps.engelsmaTuple R W d)
    (i : BoundedGaps.engelsmaTuple) : d i < R := by
  have hprod_pos : 0 < BoundedGaps.Maynard.divisorTupleProduct
      BoundedGaps.engelsmaTuple d := by
    unfold BoundedGaps.Maynard.divisorTupleProduct
    apply Finset.prod_pos
    intro j hj
    exact Nat.pos_of_ne_zero (hd.coordinate_squarefree j).ne_zero
  have hcoord_le : d i ≤ BoundedGaps.Maynard.divisorTupleProduct
      BoundedGaps.engelsmaTuple d :=
    Nat.le_of_dvd hprod_pos
      (BoundedGaps.Maynard.divisorTupleCoordinate_dvd_product d i)
  exact hcoord_le.trans_lt hd.1

theorem affinePrimeProgressionCount_eq_zero_of_coordinate_ne_one
    {c : BoundedGaps.engelsmaTuple → ℕ} {R W N : ℕ}
    {d e : BoundedGaps.engelsmaTuple → ℕ}
    (hc : ∀ i, 0 < c i)
    (hcover : CoefficientPrimesCovered c W)
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple
      BoundedGaps.engelsmaTuple R W d)
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple
      BoundedGaps.engelsmaTuple R W e)
    (hcross : BoundedGaps.Maynard.IsCrossCoordinateCoprime
      BoundedGaps.engelsmaTuple d e)
    (hRN : R + 1 ≤ N) (i : BoundedGaps.engelsmaTuple)
    (hcoord : d i ≠ 1 ∨ e i ≠ 1) :
    affinePrimeProgressionCount (c i) N
      (BoundedGaps.Maynard.divisorPairModulus
        BoundedGaps.engelsmaTuple W d e)
      (pairCrtResidue c R W d e hd he hcross) = 0 := by
  classical
  unfold affinePrimeProgressionCount
  apply Finset.card_eq_zero.mpr
  ext n
  simp only [Finset.mem_filter]
  constructor
  · intro hn
    obtain ⟨hnlower, hnupper⟩ := Finset.mem_Ico.mp hn.1
    have hpair := (modEq_pairCrtResidue_iff hcover hd he hcross n).mp hn.2.1
    have hnpos : 0 < n := by omega
    have hprodpos : 0 < c i * n := mul_pos (hc i) hnpos
    have hformlower : N - 1 ≤ c i * n - 1 := by
      apply Nat.sub_le_sub_right
      exact hnlower.trans (Nat.le_mul_of_pos_left n (hc i))
    rcases hcoord with hdi | hei
    · have hdiv : d i ∣ c i * n - 1 :=
        (Nat.modEq_iff_dvd' hprodpos).mp (hpair.2.1 i).symm
      obtain hone | hsame := (Nat.dvd_prime hn.2.2).mp hdiv
      · exact (hdi hone).elim
      · have hlt : d i < c i * n - 1 := by
          have hdr := isMaynard_coordinate_lt_radius hd i
          omega
        exact (by omega : False).elim
    · have hdiv : e i ∣ c i * n - 1 :=
        (Nat.modEq_iff_dvd' hprodpos).mp (hpair.2.2 i).symm
      obtain hone | hsame := (Nat.dvd_prime hn.2.2).mp hdiv
      · exact (hei hone).elim
      · have hlt : e i < c i * n - 1 := by
          have her := isMaynard_coordinate_lt_radius he i
          omega
        exact (by omega : False).elim
  · intro hn
    simp at hn

def affineCompatiblePairRestrictedMainOuter
    (c : BoundedGaps.engelsmaTuple → ℕ)
    (D : Finset (BoundedGaps.engelsmaTuple → ℕ)) (R W N : ℕ)
    (coeff : (BoundedGaps.engelsmaTuple → ℕ) → ℝ)
    (hD : ∀ d ∈ D, BoundedGaps.Maynard.IsMaynardDivisorTuple
      BoundedGaps.engelsmaTuple R W d) : ℝ :=
  ∑ d : D,
    ∑ e : D.filter (fun e : BoundedGaps.engelsmaTuple → ℕ ↦
      BoundedGaps.Maynard.IsCrossCoordinateCoprime
        BoundedGaps.engelsmaTuple d.1 e),
      ∑ i : BoundedGaps.engelsmaTuple,
        if d.1 i = 1 ∧ e.1 i = 1 then
          affinePrimeProgressionMainTerm (c i) N
            (BoundedGaps.Maynard.divisorPairModulus
              BoundedGaps.engelsmaTuple W d.1 e.1) *
            (coeff d.1 * coeff e.1)
        else 0

def affineCompatiblePairRestrictedErrorOuter
    (c : BoundedGaps.engelsmaTuple → ℕ)
    (D : Finset (BoundedGaps.engelsmaTuple → ℕ)) (R W N : ℕ)
    (coeff : (BoundedGaps.engelsmaTuple → ℕ) → ℝ)
    (hD : ∀ d ∈ D, BoundedGaps.Maynard.IsMaynardDivisorTuple
      BoundedGaps.engelsmaTuple R W d) : ℝ :=
  ∑ d : D,
    ∑ e : D.filter (fun e : BoundedGaps.engelsmaTuple → ℕ ↦
      BoundedGaps.Maynard.IsCrossCoordinateCoprime
        BoundedGaps.engelsmaTuple d.1 e),
      ∑ i : BoundedGaps.engelsmaTuple,
        if d.1 i = 1 ∧ e.1 i = 1 then
          affinePrimeProgressionError (c i) N
            (BoundedGaps.Maynard.divisorPairModulus
              BoundedGaps.engelsmaTuple W d.1 e.1)
            (pairCrtResidue c R W d.1 e.1
              (hD d.1 d.2)
              (hD e.1 (Finset.mem_filter.mp e.2).1)
              (Finset.mem_filter.mp e.2).2) *
            (coeff d.1 * coeff e.1)
        else 0

theorem affineCompatiblePrimeWeightedPairSum_eq_main_add_error
    {c : BoundedGaps.engelsmaTuple → ℕ}
    {D : Finset (BoundedGaps.engelsmaTuple → ℕ)} {R W N : ℕ}
    {coeff : (BoundedGaps.engelsmaTuple → ℕ) → ℝ}
    (hc : ∀ i, 0 < c i)
    (hcover : CoefficientPrimesCovered c W)
    (hD : ∀ d ∈ D, BoundedGaps.Maynard.IsMaynardDivisorTuple
      BoundedGaps.engelsmaTuple R W d)
    (hRN : R + 1 ≤ N) :
    affineCompatiblePrimeWeightedPairSum c D W N coeff =
      affineCompatiblePairRestrictedMainOuter c D R W N coeff hD +
        affineCompatiblePairRestrictedErrorOuter c D R W N coeff hD := by
  classical
  unfold affineCompatiblePrimeWeightedPairSum
    affineCompatiblePairRestrictedMainOuter
    affineCompatiblePairRestrictedErrorOuter
  rw [← Finset.sum_attach, Finset.univ_eq_attach]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hdmem
  rw [Finset.sum_filter, Finset.univ_eq_attach, ← Finset.sum_filter]
  rw [← Finset.sum_attach, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e hemel
  have heData : e.1 ∈ D ∧
      BoundedGaps.Maynard.IsCrossCoordinateCoprime
        BoundedGaps.engelsmaTuple d.1 e.1 := Finset.mem_filter.mp e.2
  have hd := hD d.1 d.2
  have he := hD e.1 heData.1
  have hcross : BoundedGaps.Maynard.IsCrossCoordinateCoprime
      BoundedGaps.engelsmaTuple d.1 e.1 := heData.2
  rw [affinePrimeWeightedPairInnerSum_eq_progressionCounts
    hcover hd he hcross coeff]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hred : d.1 i = 1 ∧ e.1 i = 1
  · simp [hred]
    rw [affinePrimeProgressionCount_decomposition]
    ring
  · have hzero := affinePrimeProgressionCount_eq_zero_of_coordinate_ne_one
      hc hcover hd he hcross hRN i (not_and_or.mp hred)
    simp [hred, hzero]

theorem affineCompatiblePairRestrictedMainOuter_eq_coordinate_sum
    {c : BoundedGaps.engelsmaTuple → ℕ}
    {D : Finset (BoundedGaps.engelsmaTuple → ℕ)} {R W N : ℕ}
    {coeff : (BoundedGaps.engelsmaTuple → ℕ) → ℝ}
    (hc : ∀ i, 0 < c i)
    (hcover : CoefficientPrimesCovered c W)
    (hD : ∀ d ∈ D, BoundedGaps.Maynard.IsMaynardDivisorTuple
      BoundedGaps.engelsmaTuple R W d) :
    affineCompatiblePairRestrictedMainOuter c D R W N coeff hD =
      ∑ i : BoundedGaps.engelsmaTuple,
        (affinePrimeIntervalCount (c i) N / c i) *
          BoundedGaps.Maynard.restrictedMainArithmeticCoefficient
            BoundedGaps.engelsmaTuple D W coeff i := by
  classical
  let term (d : D)
      (e : D.filter (fun e : BoundedGaps.engelsmaTuple → ℕ ↦
        BoundedGaps.Maynard.IsCrossCoordinateCoprime
          BoundedGaps.engelsmaTuple d.1 e))
      (i : BoundedGaps.engelsmaTuple) : ℝ :=
    if d.1 i = 1 ∧ e.1 i = 1 then
      affinePrimeProgressionMainTerm (c i) N
        (BoundedGaps.Maynard.divisorPairModulus
          BoundedGaps.engelsmaTuple W d.1 e.1) *
        (coeff d.1 * coeff e.1)
    else 0
  have hleft :
      affineCompatiblePairRestrictedMainOuter c D R W N coeff hD =
        ∑ d : D,
          ∑ e : D.filter (fun e : BoundedGaps.engelsmaTuple → ℕ ↦
            BoundedGaps.Maynard.IsCrossCoordinateCoprime
              BoundedGaps.engelsmaTuple d.1 e),
            ∑ i : BoundedGaps.engelsmaTuple, term d e i := by
    unfold affineCompatiblePairRestrictedMainOuter
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro e he
    rfl
  rw [hleft]
  have hswap :
      (∑ d : D,
        ∑ e : D.filter (fun e : BoundedGaps.engelsmaTuple → ℕ ↦
          BoundedGaps.Maynard.IsCrossCoordinateCoprime
            BoundedGaps.engelsmaTuple d.1 e),
          ∑ i : BoundedGaps.engelsmaTuple, term d e i) =
      ∑ i : BoundedGaps.engelsmaTuple,
        ∑ d : D,
          ∑ e : D.filter (fun e : BoundedGaps.engelsmaTuple → ℕ ↦
            BoundedGaps.Maynard.IsCrossCoordinateCoprime
              BoundedGaps.engelsmaTuple d.1 e), term d e i := by
    calc
      _ = ∑ d : D,
          ∑ i : BoundedGaps.engelsmaTuple,
            ∑ e : D.filter (fun e : BoundedGaps.engelsmaTuple → ℕ ↦
              BoundedGaps.Maynard.IsCrossCoordinateCoprime
                BoundedGaps.engelsmaTuple d.1 e), term d e i := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [Finset.sum_comm]
      _ = _ := Finset.sum_comm
  rw [hswap]
  apply Finset.sum_congr rfl
  intro i hi
  unfold BoundedGaps.Maynard.restrictedMainArithmeticCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hdmem
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e hemel
  by_cases hred : d.1 i = 1 ∧ e.1 i = 1
  · dsimp only [term]
    rw [if_pos hred, if_pos hred]
    rw [affinePrimeProgressionMainTerm_eq hcover i d.1 e.1 (hc i)]
    ring
  · dsimp only [term]
    rw [if_neg hred, if_neg hred]
    simp

def affineMaynardS2Main
    (c : BoundedGaps.engelsmaTuple → ℕ) (alpha : ℝ) (N : ℕ) : ℝ :=
  ∑ i : BoundedGaps.engelsmaTuple,
    (affinePrimeIntervalCount (c i) N / c i) *
      BoundedGaps.Maynard.engelsmaMaynardS2ShiftKernel alpha N i

theorem affineMaynardS2SupportProof (alpha : ℝ) (N : ℕ) :
    ∀ d ∈ affineMaynardSupport alpha N,
      BoundedGaps.Maynard.IsMaynardDivisorTuple
        BoundedGaps.engelsmaTuple
        (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
        (BoundedGaps.Maynard.engelsmaMaynardModulus N) d := by
  unfold affineMaynardSupport
  exact BoundedGaps.Maynard.engelsmaMaynardS2SupportProof alpha N

theorem affineConcreteRestrictedMainOuter_eq_affineMaynardS2Main
    {c : BoundedGaps.engelsmaTuple → ℕ} (hc : ∀ i, 0 < c i)
    {alpha : ℝ} {N : ℕ}
    (hcover : CoefficientPrimesCovered c
      (BoundedGaps.Maynard.engelsmaMaynardModulus N)) :
    affineCompatiblePairRestrictedMainOuter c
      (affineMaynardSupport alpha N)
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
      (BoundedGaps.Maynard.engelsmaMaynardModulus N) N
      (affineMaynardCoefficient alpha N)
      (affineMaynardS2SupportProof alpha N) =
        affineMaynardS2Main c alpha N := by
  rw [affineCompatiblePairRestrictedMainOuter_eq_coordinate_sum
    hc hcover]
  unfold affineMaynardS2Main affineMaynardSupport affineMaynardCoefficient
  apply Finset.sum_congr rfl
  intro i hi
  rw [BoundedGaps.Maynard.engelsmaMaynardS2ShiftKernel_eq_restrictedMainArithmeticCoefficient]

/-! ## Prime-number-theorem factor for a fixed leading coefficient -/

theorem tendsto_nat_mul_atTop {a : ℕ} (ha : 0 < a) :
    Tendsto (fun N : ℕ ↦ a * N) atTop atTop := by
  have h := (show Tendsto (fun N : ℕ ↦ N) atTop atTop from tendsto_id).nsmul_atTop ha
  simpa [nsmul_eq_mul, mul_comm] using h

theorem tendsto_log_nat_mul_sub_one_div_log_sub_one
    {a : ℕ} (ha : 0 < a) :
    Tendsto (fun N : ℕ ↦
      Real.log ((a * N - 1 : ℕ) : ℝ) /
        Real.log ((N - 1 : ℕ) : ℝ)) atTop (nhds 1) := by
  have hinv : Tendsto (fun N : ℕ ↦ (1 : ℝ) / (N : ℝ))
      atTop (nhds 0) := tendsto_const_div_atTop_nhds_zero_nat 1
  have hnumRatio : Tendsto (fun N : ℕ ↦
      ((a * N - 1 : ℕ) : ℝ) / (N : ℝ)) atTop (nhds (a : ℝ)) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (a : ℝ))
      atTop (nhds (a : ℝ))).sub hinv
    have heq : (fun N : ℕ ↦ (a : ℝ) - 1 / (N : ℝ)) =ᶠ[atTop]
        (fun N : ℕ ↦ ((a * N - 1 : ℕ) : ℝ) / (N : ℝ)) := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
      rw [Nat.cast_sub (show 1 ≤ a * N by
        exact Nat.one_le_iff_ne_zero.mpr (mul_ne_zero ha.ne' (by omega)))]
      push_cast
      field_simp [hN0]
    simpa using h.congr' heq
  have hdenRatio : Tendsto (fun N : ℕ ↦
      ((N - 1 : ℕ) : ℝ) / (N : ℝ)) atTop (nhds 1) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ))
      atTop (nhds 1)).sub hinv
    have heq : (fun N : ℕ ↦ (1 : ℝ) - 1 / (N : ℝ)) =ᶠ[atTop]
        (fun N : ℕ ↦ ((N - 1 : ℕ) : ℝ) / (N : ℝ)) := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
      rw [Nat.cast_sub hN]
      field_simp [hN0]
      norm_num
    simpa using h.congr' heq
  have hendpointRatio : Tendsto (fun N : ℕ ↦
      ((a * N - 1 : ℕ) : ℝ) / ((N - 1 : ℕ) : ℝ))
      atTop (nhds (a : ℝ)) := by
    have h := hnumRatio.div hdenRatio one_ne_zero
    have heq : ((fun N : ℕ ↦ ((a * N - 1 : ℕ) : ℝ) / (N : ℝ)) /
        (fun N : ℕ ↦ ((N - 1 : ℕ) : ℝ) / (N : ℝ))) =ᶠ[atTop]
        (fun N : ℕ ↦ ((a * N - 1 : ℕ) : ℝ) / ((N - 1 : ℕ) : ℝ)) := by
      filter_upwards [eventually_ge_atTop 3] with N hN
      have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
      have hsub0 : ((N - 1 : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (show N - 1 ≠ 0 by omega)
      simp only [Pi.div_apply]
      field_simp [hN0, hsub0]
    simpa using h.congr' heq
  have hlogEndpointRatio : Tendsto (fun N : ℕ ↦ Real.log
      (((a * N - 1 : ℕ) : ℝ) / ((N - 1 : ℕ) : ℝ)))
      atTop (nhds (Real.log (a : ℝ))) :=
    (Real.continuousAt_log (by exact_mod_cast ha.ne')).tendsto.comp hendpointRatio
  have hlogDiff : Tendsto (fun N : ℕ ↦
      Real.log ((a * N - 1 : ℕ) : ℝ) -
        Real.log ((N - 1 : ℕ) : ℝ))
      atTop (nhds (Real.log (a : ℝ))) := by
    apply hlogEndpointRatio.congr'
    filter_upwards [eventually_ge_atTop 2] with N hN
    apply Real.log_div
    · exact_mod_cast (show a * N - 1 ≠ 0 by
        have : 1 < a * N := lt_of_lt_of_le hN (Nat.le_mul_of_pos_left N ha)
        omega)
    · exact_mod_cast (show N - 1 ≠ 0 by omega)
  have hbaseAtTop : Tendsto (fun N : ℕ ↦ ((N - 1 : ℕ) : ℝ))
      atTop atTop := tendsto_natCast_atTop_atTop.comp (tendsto_sub_atTop_nat 1)
  have hlogBase : Tendsto (fun N : ℕ ↦ Real.log ((N - 1 : ℕ) : ℝ))
      atTop atTop := Real.tendsto_log_atTop.comp hbaseAtTop
  have herror : Tendsto (fun N : ℕ ↦
      (Real.log ((a * N - 1 : ℕ) : ℝ) -
        Real.log ((N - 1 : ℕ) : ℝ)) /
          Real.log ((N - 1 : ℕ) : ℝ)) atTop (nhds 0) :=
    hlogDiff.div_atTop hlogBase
  have hsum := (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ))
    atTop (nhds 1)).add herror
  have heq : (fun N : ℕ ↦ (1 : ℝ) +
      (Real.log ((a * N - 1 : ℕ) : ℝ) -
        Real.log ((N - 1 : ℕ) : ℝ)) /
          Real.log ((N - 1 : ℕ) : ℝ)) =ᶠ[atTop]
      (fun N : ℕ ↦ Real.log ((a * N - 1 : ℕ) : ℝ) /
        Real.log ((N - 1 : ℕ) : ℝ)) := by
    filter_upwards [hlogBase.eventually (eventually_ne_atTop 0)] with N hlog0
    field_simp [hlog0]
    ring
  simpa using hsum.congr' heq

theorem tendsto_log_affineRadius_div_log_nat_mul_sub_one
    {a : ℕ} (ha : 0 < a) {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (fun N : ℕ ↦
      Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) /
        Real.log ((a * N - 1 : ℕ) : ℝ)) atTop (nhds alpha) := by
  have hbase := BoundedGaps.Maynard.tendsto_log_engelsmaMaynardRadius_div_log_sub halpha
  have hscale := tendsto_log_nat_mul_sub_one_div_log_sub_one ha
  have h := hbase.div hscale one_ne_zero
  have heq : ((fun N : ℕ ↦
      Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) /
        Real.log ((N - 1 : ℕ) : ℝ)) /
      (fun N : ℕ ↦ Real.log ((a * N - 1 : ℕ) : ℝ) /
        Real.log ((N - 1 : ℕ) : ℝ))) =ᶠ[atTop]
      (fun N : ℕ ↦
        Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) /
          Real.log ((a * N - 1 : ℕ) : ℝ)) := by
    filter_upwards [eventually_ge_atTop 2,
    (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_sub_atTop_nat 1))).eventually
        (eventually_ne_atTop 0)] with N hN hlog0
    simp only [Function.comp_apply] at hlog0
    simp only [Pi.div_apply]
    field_simp [hlog0]
  simpa using h.congr' heq

private theorem cast_prime_filter_Ico_eq_primeCount_sub
    {A B : ℕ} (hA : 0 < A) (hAB : A ≤ B) :
    (((Finset.Ico A B).filter Nat.Prime).card : ℝ) =
      (BoundedGaps.Maynard.primeCountTotal (B - 1) : ℝ) -
        (BoundedGaps.Maynard.primeCountTotal (A - 1) : ℝ) := by
  have hAeq : A - 1 + 1 = A := by omega
  have hBeq : B - 1 + 1 = B := by omega
  unfold BoundedGaps.Maynard.primeCountTotal Nat.primeCounting Nat.primeCounting'
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  rw [Finset.natCast_card_filter, Finset.natCast_card_filter,
    Finset.natCast_card_filter]
  simpa [hAeq, hBeq] using Finset.sum_Ico_eq_sub
    (f := fun n : ℕ ↦ if n.Prime then (1 : ℝ) else 0) hAB

private theorem abs_primeCountTotal_add_sub_le (x h : ℕ) :
    |(BoundedGaps.Maynard.primeCountTotal (x + h) : ℝ) -
      (BoundedGaps.Maynard.primeCountTotal x : ℝ)| ≤ (h : ℝ) := by
  have hcard := cast_prime_filter_Ico_eq_primeCount_sub
    (A := x + 1) (B := x + h + 1) (by omega) (by omega)
  have hsubset : (Finset.Ico (x + 1) (x + h + 1)).filter Nat.Prime ⊆
      Finset.Ico (x + 1) (x + h + 1) := Finset.filter_subset _ _
  have hcardNat := Finset.card_le_card hsubset
  rw [Nat.card_Ico] at hcardNat
  have hcardReal :
      (((Finset.Ico (x + 1) (x + h + 1)).filter Nat.Prime).card : ℝ) ≤ h := by
    exact_mod_cast (show
      ((Finset.Ico (x + 1) (x + h + 1)).filter Nat.Prime).card ≤ h by omega)
  have heq :
      (((Finset.Ico (x + 1) (x + h + 1)).filter Nat.Prime).card : ℝ) =
        (BoundedGaps.Maynard.primeCountTotal (x + h) : ℝ) -
          (BoundedGaps.Maynard.primeCountTotal x : ℝ) := by
    simpa only [Nat.add_sub_cancel, Nat.add_sub_cancel_left] using hcard
  rw [← heq, abs_of_nonneg (by positivity)]
  exact hcardReal

theorem abs_affinePrimeIntervalCount_sub_scaledInterval_le
    {a N : ℕ} (ha : 0 < a) (hN : 1 < N) :
    |affinePrimeIntervalCount a N -
        (BoundedGaps.Maynard.primeCountTotalInInterval (a * N) : ℝ)| ≤ 2 := by
  have hinterval := BoundedGaps.Maynard.cast_primeCountTotalInInterval
    (show 0 < a * N from mul_pos ha (by omega))
  unfold affinePrimeIntervalCount
  rw [hinterval]
  have hu := abs_primeCountTotal_add_sub_le (a * (2 * N) - 2) 1
  have hl := abs_primeCountTotal_add_sub_le (a * N - 2) 1
  norm_num at hu hl
  have hau : 2 * (a * N) - 1 = (a * (2 * N) - 2) + 1 := by
    rw [show 2 * (a * N) = a * (2 * N) by ring]
    have : 1 < a * (2 * N) := by
      have : 1 < 2 * N := by omega
      exact lt_of_lt_of_le this (Nat.le_mul_of_pos_left _ ha)
    omega
  have hal : a * N - 1 = (a * N - 2) + 1 := by
    have : 1 < a * N := lt_of_lt_of_le hN (Nat.le_mul_of_pos_left N ha)
    omega
  rw [hau, hal]
  have hrearrange :
      ((BoundedGaps.Maynard.primeCountTotal (a * (2 * N) - 2) : ℝ) -
          (BoundedGaps.Maynard.primeCountTotal (a * N - 2) : ℝ)) -
        ((BoundedGaps.Maynard.primeCountTotal
            ((a * (2 * N) - 2) + 1) : ℝ) -
          (BoundedGaps.Maynard.primeCountTotal ((a * N - 2) + 1) : ℝ)) =
        -((BoundedGaps.Maynard.primeCountTotal
            ((a * (2 * N) - 2) + 1) : ℝ) -
          (BoundedGaps.Maynard.primeCountTotal (a * (2 * N) - 2) : ℝ)) +
        ((BoundedGaps.Maynard.primeCountTotal ((a * N - 2) + 1) : ℝ) -
          (BoundedGaps.Maynard.primeCountTotal (a * N - 2) : ℝ)) := by ring
  rw [hrearrange]
  calc
    |_ + _| ≤
        |(BoundedGaps.Maynard.primeCountTotal
            ((a * (2 * N) - 2) + 1) : ℝ) -
          (BoundedGaps.Maynard.primeCountTotal (a * (2 * N) - 2) : ℝ)| +
        |(BoundedGaps.Maynard.primeCountTotal ((a * N - 2) + 1) : ℝ) -
          (BoundedGaps.Maynard.primeCountTotal (a * N - 2) : ℝ)| := by
          simpa only [abs_neg] using abs_add_le
            (-((BoundedGaps.Maynard.primeCountTotal
              ((a * (2 * N) - 2) + 1) : ℝ) -
              (BoundedGaps.Maynard.primeCountTotal (a * (2 * N) - 2) : ℝ)))
            ((BoundedGaps.Maynard.primeCountTotal ((a * N - 2) + 1) : ℝ) -
              (BoundedGaps.Maynard.primeCountTotal (a * N - 2) : ℝ))
    _ ≤ 1 + 1 := add_le_add hu hl
    _ = 2 := by norm_num

theorem tendsto_affinePrimeIntervalFactor_of_pnt
    {a : ℕ} (ha : 0 < a) {alpha : ℝ} (halpha : 0 < alpha)
    (hpnt : Tendsto
      (fun n : ℕ ↦
        (BoundedGaps.Maynard.primeCountTotal n : ℝ) *
          Real.log (n : ℝ) / (n : ℝ)) atTop (nhds 1)) :
    Tendsto (fun N : ℕ ↦
      ((affinePrimeIntervalCount a N / a) / (N : ℝ)) *
        Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N))
      atTop (nhds alpha) := by
  have hintervalBase :=
    BoundedGaps.Maynard.tendsto_primeCountTotalInInterval_div_mul_log_sub_of_pnt hpnt
  have hinterval : Tendsto (fun N : ℕ ↦
      (BoundedGaps.Maynard.primeCountTotalInInterval (a * N) : ℝ) /
          (a * N : ℕ) * Real.log ((a * N - 1 : ℕ) : ℝ))
      atTop (nhds 1) := by
    simpa [Function.comp_def] using
      hintervalBase.comp (tendsto_nat_mul_atTop ha)
  have hlog := tendsto_log_affineRadius_div_log_nat_mul_sub_one
    ha halpha
  have happroxProduct := hinterval.mul hlog
  have happrox : Tendsto (fun N : ℕ ↦
      (BoundedGaps.Maynard.primeCountTotalInInterval (a * N) : ℝ) /
          (a * N : ℕ) *
        Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N))
      atTop (nhds alpha) := by
    have heq : (fun N : ℕ ↦
        ((BoundedGaps.Maynard.primeCountTotalInInterval (a * N) : ℝ) /
            (a * N : ℕ) * Real.log ((a * N - 1 : ℕ) : ℝ)) *
          (Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) /
            Real.log ((a * N - 1 : ℕ) : ℝ))) =ᶠ[atTop]
        (fun N : ℕ ↦
          (BoundedGaps.Maynard.primeCountTotalInInterval (a * N) : ℝ) /
              (a * N : ℕ) *
            Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)) := by
      filter_upwards [eventually_ge_atTop 3] with N hN
      have hlog0 : Real.log ((a * N - 1 : ℕ) : ℝ) ≠ 0 := by
        apply ne_of_gt
        apply Real.log_pos
        exact_mod_cast (show 1 < a * N - 1 by
          have : 2 < a * N := lt_of_lt_of_le (by omega : 2 < N)
            (Nat.le_mul_of_pos_left N ha)
          omega)
      field_simp [hlog0]
    simpa using happroxProduct.congr' heq
  have hscaledLog : Tendsto (fun N : ℕ ↦
      Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) /
        ((a : ℝ) * (N : ℝ))) atTop (nhds 0) := by
    have h :=
      (BoundedGaps.Maynard.tendsto_log_engelsmaMaynardRadius_div_natCast_zero
        halpha).div_const (a : ℝ)
    have heq : (fun N : ℕ ↦
        Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) /
          (N : ℝ) / (a : ℝ)) =ᶠ[atTop]
        (fun N : ℕ ↦
          Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) /
            ((a : ℝ) * (N : ℝ))) := by
      filter_upwards [] with N
      ring
    simpa using h.congr' heq
  have henv : Tendsto (fun N : ℕ ↦ 2 *
      |Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) /
        ((a : ℝ) * (N : ℝ))|) atTop (nhds 0) := by
    simpa using hscaledLog.abs.const_mul 2
  have herr : Tendsto (fun N : ℕ ↦
      ((affinePrimeIntervalCount a N / a) / (N : ℝ)) *
          Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) -
        (BoundedGaps.Maynard.primeCountTotalInInterval (a * N) : ℝ) /
            (a * N : ℕ) *
          Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N))
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ ↦ abs_nonneg _) ?_ henv
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hbound := abs_affinePrimeIntervalCount_sub_scaledInterval_le
      ha hN
    have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    rw [show
      ((affinePrimeIntervalCount a N / a) / (N : ℝ)) *
            Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) -
          (BoundedGaps.Maynard.primeCountTotalInInterval (a * N) : ℝ) /
              (a * N : ℕ) *
            Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) =
        (affinePrimeIntervalCount a N -
          (BoundedGaps.Maynard.primeCountTotalInInterval (a * N) : ℝ)) *
          (Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) /
            ((a : ℝ) * (N : ℝ))) by
        push_cast
        field_simp [ha0, hN0]
        ]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hbound (abs_nonneg _)
  have hsum := herr.add happrox
  have heq : (fun N : ℕ ↦
      (((affinePrimeIntervalCount a N / a) / (N : ℝ)) *
          Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) -
        (BoundedGaps.Maynard.primeCountTotalInInterval (a * N) : ℝ) /
            (a * N : ℕ) *
          Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)) +
        (BoundedGaps.Maynard.primeCountTotalInInterval (a * N) : ℝ) /
            (a * N : ℕ) *
          Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)) =ᶠ[atTop]
      (fun N : ℕ ↦ ((affinePrimeIntervalCount a N / a) / (N : ℝ)) *
        Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)) := by
    filter_upwards [] with N
    ring
  simpa using hsum.congr' heq

theorem affineMaynardS2Main_eq_invTotient_mul_coordinateOne_sub_cross_sum
    (c : BoundedGaps.engelsmaTuple → ℕ) (alpha : ℝ) (N : ℕ) :
    affineMaynardS2Main c alpha N =
      ∑ i : BoundedGaps.engelsmaTuple,
        (affinePrimeIntervalCount (c i) N / c i) *
          ((Nat.totient (BoundedGaps.Maynard.engelsmaMaynardModulus N) : ℝ)⁻¹ *
            (BoundedGaps.Maynard.engelsmaMaynardS2CoordinateOneYDiagonal
                alpha N i -
              BoundedGaps.Maynard.engelsmaMaynardS2RestrictedCrossCorrection
                alpha N i)) := by
  unfold affineMaynardS2Main
  apply Finset.sum_congr rfl
  intro i hi
  rw [BoundedGaps.Maynard.engelsmaMaynardS2ShiftKernel_eq_invTotient_mul_GKernel]
  rw [BoundedGaps.Maynard.engelsmaMaynardS2RestrictedGKernel_eq_quadratic_sub_cross]
  rw [BoundedGaps.Maynard.engelsmaMaynardS2RestrictedQuadratic_eq_yDiagonal]
  rw [BoundedGaps.Maynard.engelsmaMaynardS2RestrictedYDiagonal_eq_coordinateOne]

def affineMaynardS2GoodComplementMain
    (c : BoundedGaps.engelsmaTuple → ℕ) (alpha : ℝ) (N : ℕ) : ℝ :=
  ∑ i : BoundedGaps.engelsmaTuple,
    (affinePrimeIntervalCount (c i) N / c i) *
      ((Nat.totient (BoundedGaps.Maynard.engelsmaMaynardModulus N) : ℝ)⁻¹ *
        (BoundedGaps.Maynard.preSieveSingularSeries
            (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) ^ 2 *
          BoundedGaps.Maynard.engelsmaS2CoordinateFiberGoodComplementOuterMoment
            (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
            (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) i))

private theorem affineGoodComplementTerm_div_scale_eq
    {A phi W N L Lreal S M : ℝ}
    (hW : W ≠ 0) (hN : N ≠ 0) (hL : L ≠ 0)
    (hLreal : Lreal ≠ 0) (hphi : phi ≠ 0)
    (hS : S = phi / W) :
    A * (phi⁻¹ * (S ^ 2 * M)) /
        ((phi ^ 105 * N * Lreal ^ 105) / W ^ 106) =
      (A / N) * (M / ((S * L) ^ 104 * L ^ 2)) * L *
        (L / Lreal) ^ 105 := by
  rw [hS]
  field_simp [hW, hN, hL, hLreal, hphi]

theorem affineMaynardS2GoodComplementMain_div_scale_eq
    {c : BoundedGaps.engelsmaTuple → ℕ} {alpha : ℝ} {N : ℕ}
    (hN : 0 < N)
    (hR : 1 < BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
    (hRreal : 1 < BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N) :
    affineMaynardS2GoodComplementMain c alpha N /
        BoundedGaps.Maynard.engelsmaMaynardScale alpha N =
      ∑ i : BoundedGaps.engelsmaTuple,
        ((affinePrimeIntervalCount (c i) N / c i) / (N : ℝ)) *
          BoundedGaps.Maynard.normalizedEngelsmaS2CoordinateFiberGoodComplementOuterMoment
            alpha N i *
          Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) *
          (Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) /
            Real.log (BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N)) ^ 105 := by
  let W := BoundedGaps.Maynard.engelsmaMaynardModulus N
  let D := BoundedGaps.Maynard.tripleLogCutoff (N - 1)
  let R := BoundedGaps.Maynard.engelsmaMaynardRadius alpha N
  let Rreal := BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N
  let L := Real.log R
  let Lreal := Real.log Rreal
  let S := BoundedGaps.Maynard.preSieveSingularSeries D
  have hWnat : 0 < W := by
    dsimp [W]
    exact primorial_pos _
  have hW : (W : ℝ) ≠ 0 := by exact_mod_cast hWnat.ne'
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hphi : (Nat.totient W : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hWnat).ne'
  have hL : L ≠ 0 := by
    exact (Real.log_pos (by exact_mod_cast hR)).ne'
  have hLreal : Lreal ≠ 0 := (Real.log_pos hRreal).ne'
  have hS : S = (Nat.totient W : ℝ) / (W : ℝ) := by
    dsimp [S, W, D]
    rw [show BoundedGaps.Maynard.engelsmaMaynardModulus N =
        primorial
          (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) by rfl]
    simpa using BoundedGaps.Maynard.preSieveSingularSeries_eq_totient_div
      (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
  unfold affineMaynardS2GoodComplementMain
    BoundedGaps.Maynard.engelsmaMaynardScale
    BoundedGaps.Maynard.maynardSieveScale
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hcard : ((Finset.univ : Finset BoundedGaps.engelsmaTuple).erase i).card = 104 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
    simpa using BoundedGaps.engelsmaTuple_card
  unfold BoundedGaps.Maynard.normalizedEngelsmaS2CoordinateFiberGoodComplementOuterMoment
  rw [hcard]
  simpa only [Nat.reduceAdd] using
    (affineGoodComplementTerm_div_scale_eq
      (A := affinePrimeIntervalCount (c i) N / c i)
      (phi := (Nat.totient W : ℝ)) (W := (W : ℝ)) (N := (N : ℝ))
      (L := L) (Lreal := Lreal) (S := S)
      (M := BoundedGaps.Maynard.engelsmaS2CoordinateFiberGoodComplementOuterMoment
        R D i) hW hNreal hL hLreal hphi hS)

theorem tendsto_affineMaynardS2GoodComplementMain_div_scale_of_pnt
    {c : BoundedGaps.engelsmaTuple → ℕ} (hc : ∀ i, 0 < c i)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hpnt : Tendsto
      (fun n : ℕ ↦
        (BoundedGaps.Maynard.primeCountTotal n : ℝ) *
          Real.log (n : ℝ) / (n : ℝ)) atTop (nhds 1)) :
    Tendsto (fun N : ℕ ↦
      affineMaynardS2GoodComplementMain c alpha N /
        BoundedGaps.Maynard.engelsmaMaynardScale alpha N)
      atTop (nhds (alpha *
        (∑ i : BoundedGaps.engelsmaTuple,
          BoundedGaps.Maynard.engelsmaS2GoodOuterFaceLimit i))) := by
  have hratio :=
    (BoundedGaps.Maynard.tendsto_log_engelsmaMaynardRadius_div_realRadius
      halpha).pow 105
  have hterm : ∀ i : BoundedGaps.engelsmaTuple,
      Tendsto (fun N : ℕ ↦
        (((affinePrimeIntervalCount (c i) N / c i) / (N : ℝ)) *
          Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)) *
          BoundedGaps.Maynard.normalizedEngelsmaS2CoordinateFiberGoodComplementOuterMoment
            alpha N i *
          (Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) /
            Real.log (BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N)) ^ 105)
        atTop (nhds (alpha *
          BoundedGaps.Maynard.engelsmaS2GoodOuterFaceLimit i)) := by
    intro i
    have hprime := tendsto_affinePrimeIntervalFactor_of_pnt
      (hc i) halpha hpnt
    have hmoment :=
      BoundedGaps.Maynard.tendsto_normalizedEngelsmaS2CoordinateFiberGoodComplementOuterMoment
        halpha i
    have hmul := (hprime.mul hmoment).mul hratio
    simpa [BoundedGaps.Maynard.engelsmaS2GoodOuterFaceLimit,
      mul_assoc, mul_left_comm, mul_comm] using hmul
  have hsum : Tendsto (fun N : ℕ ↦
      ∑ i : BoundedGaps.engelsmaTuple,
        (((affinePrimeIntervalCount (c i) N / c i) / (N : ℝ)) *
          Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)) *
          BoundedGaps.Maynard.normalizedEngelsmaS2CoordinateFiberGoodComplementOuterMoment
            alpha N i *
          (Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) /
            Real.log (BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N)) ^ 105)
      atTop (nhds (∑ i : BoundedGaps.engelsmaTuple,
        alpha * BoundedGaps.Maynard.engelsmaS2GoodOuterFaceLimit i)) := by
    apply tendsto_finsetSum
    intro i hi
    exact hterm i
  have hsum' : Tendsto (fun N : ℕ ↦
      ∑ i : BoundedGaps.engelsmaTuple,
        (((affinePrimeIntervalCount (c i) N / c i) / (N : ℝ)) *
          Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)) *
          BoundedGaps.Maynard.normalizedEngelsmaS2CoordinateFiberGoodComplementOuterMoment
            alpha N i *
          (Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) /
            Real.log (BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N)) ^ 105)
      atTop (nhds (alpha * ∑ i : BoundedGaps.engelsmaTuple,
        BoundedGaps.Maynard.engelsmaS2GoodOuterFaceLimit i)) := by
    simpa [Finset.mul_sum] using hsum
  apply hsum'.congr'
  filter_upwards [eventually_ge_atTop 1,
    BoundedGaps.Maynard.eventually_one_lt_engelsmaMaynardRadius halpha,
    eventually_ge_atTop 3] with N hN hR hN3
  have hRreal : 1 < BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N := by
    unfold BoundedGaps.Maynard.engelsmaMaynardRealRadius
      BoundedGaps.Maynard.maynardRealCutoff
    apply Real.one_lt_rpow
    · exact_mod_cast (show 1 < N - 1 by omega)
    · exact halpha
  rw [affineMaynardS2GoodComplementMain_div_scale_eq
    (show 0 < N by omega) hR hRreal]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private theorem affineMainErrorTerm_div_scale_eq
    {A phi W N L Lreal S T M : ℝ}
    (hW : W ≠ 0) (hN : N ≠ 0) (hL : L ≠ 0)
    (hLreal : Lreal ≠ 0) (hphi : phi ≠ 0)
    (hS : S = phi / W) :
    (A * (phi⁻¹ * T) - A * (phi⁻¹ * (S ^ 2 * M))) /
        ((phi ^ 105 * N * Lreal ^ 105) / W ^ 106) =
      ((A / N) * L) * ((T - S ^ 2 * M) / (S * L) ^ 106) *
        (L / Lreal) ^ 105 := by
  rw [hS]
  field_simp [hW, hN, hL, hLreal, hphi]

theorem affineMaynardS2Main_sub_goodComplementMain_div_scale_eq
    {c : BoundedGaps.engelsmaTuple → ℕ} {alpha : ℝ} {N : ℕ}
    (hN : 0 < N)
    (hR : 1 < BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
    (hRreal : 1 < BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N) :
    (affineMaynardS2Main c alpha N -
        affineMaynardS2GoodComplementMain c alpha N) /
        BoundedGaps.Maynard.engelsmaMaynardScale alpha N =
      ∑ i : BoundedGaps.engelsmaTuple,
        ((((affinePrimeIntervalCount (c i) N / c i) / (N : ℝ)) *
            Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)) *
          (((BoundedGaps.Maynard.engelsmaMaynardS2CoordinateOneYDiagonal
                  alpha N i -
                BoundedGaps.Maynard.engelsmaMaynardS2RestrictedCrossCorrection
                  alpha N i) -
              BoundedGaps.Maynard.preSieveSingularSeries
                  (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) ^ 2 *
                BoundedGaps.Maynard.engelsmaS2CoordinateFiberGoodComplementOuterMoment
                  (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
                  (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) i) /
            (BoundedGaps.Maynard.preSieveSingularSeries
                (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) *
              Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)) ^ 106) *
          (Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) /
            Real.log (BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N)) ^ 105) := by
  let W := BoundedGaps.Maynard.engelsmaMaynardModulus N
  let D := BoundedGaps.Maynard.tripleLogCutoff (N - 1)
  let R := BoundedGaps.Maynard.engelsmaMaynardRadius alpha N
  let Rreal := BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N
  let L := Real.log R
  let Lreal := Real.log Rreal
  let S := BoundedGaps.Maynard.preSieveSingularSeries D
  have hWnat : 0 < W := by
    dsimp [W]
    exact primorial_pos _
  have hW : (W : ℝ) ≠ 0 := by exact_mod_cast hWnat.ne'
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hphi : (Nat.totient W : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hWnat).ne'
  have hL : L ≠ 0 := (Real.log_pos (by exact_mod_cast hR)).ne'
  have hLreal : Lreal ≠ 0 := (Real.log_pos hRreal).ne'
  have hS : S = (Nat.totient W : ℝ) / (W : ℝ) := by
    dsimp [S, W, D]
    rw [show BoundedGaps.Maynard.engelsmaMaynardModulus N =
        primorial (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) by rfl]
    simpa using BoundedGaps.Maynard.preSieveSingularSeries_eq_totient_div
      (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
  rw [affineMaynardS2Main_eq_invTotient_mul_coordinateOne_sub_cross_sum]
  unfold affineMaynardS2GoodComplementMain
    BoundedGaps.Maynard.engelsmaMaynardScale
    BoundedGaps.Maynard.maynardSieveScale
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  simpa only [Nat.reduceAdd] using
    (affineMainErrorTerm_div_scale_eq
      (A := affinePrimeIntervalCount (c i) N / c i)
      (phi := (Nat.totient W : ℝ)) (W := (W : ℝ)) (N := (N : ℝ))
      (L := L) (Lreal := Lreal) (S := S)
      (T := BoundedGaps.Maynard.engelsmaMaynardS2CoordinateOneYDiagonal
          alpha N i -
        BoundedGaps.Maynard.engelsmaMaynardS2RestrictedCrossCorrection
          alpha N i)
      (M := BoundedGaps.Maynard.engelsmaS2CoordinateFiberGoodComplementOuterMoment
        R D i) hW hNreal hL hLreal hphi hS)

theorem tendsto_affineMaynardS2Main_sub_goodComplementMain_div_scale_zero
    {c : BoundedGaps.engelsmaTuple → ℕ} (hc : ∀ i, 0 < c i)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hpnt : Tendsto
      (fun n : ℕ ↦
        (BoundedGaps.Maynard.primeCountTotal n : ℝ) *
          Real.log (n : ℝ) / (n : ℝ)) atTop (nhds 1)) :
    Tendsto (fun N : ℕ ↦
      (affineMaynardS2Main c alpha N -
        affineMaynardS2GoodComplementMain c alpha N) /
          BoundedGaps.Maynard.engelsmaMaynardScale alpha N)
      atTop (nhds 0) := by
  have hratio :=
    (BoundedGaps.Maynard.tendsto_log_engelsmaMaynardRadius_div_realRadius
      halpha).pow 105
  have hterm : ∀ i : BoundedGaps.engelsmaTuple,
      Tendsto (fun N : ℕ ↦
        ((((affinePrimeIntervalCount (c i) N / c i) / (N : ℝ)) *
            Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)) *
          (((BoundedGaps.Maynard.engelsmaMaynardS2CoordinateOneYDiagonal
                  alpha N i -
                BoundedGaps.Maynard.engelsmaMaynardS2RestrictedCrossCorrection
                  alpha N i) -
              BoundedGaps.Maynard.preSieveSingularSeries
                  (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) ^ 2 *
                BoundedGaps.Maynard.engelsmaS2CoordinateFiberGoodComplementOuterMoment
                  (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
                  (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) i) /
            (BoundedGaps.Maynard.preSieveSingularSeries
                (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) *
              Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)) ^ 106) *
          (Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) /
            Real.log (BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N)) ^ 105))
        atTop (nhds 0) := by
    intro i
    have hprime := tendsto_affinePrimeIntervalFactor_of_pnt
      (hc i) halpha hpnt
    have hkernel :=
      BoundedGaps.Maynard.tendsto_normalizedEngelsmaS2CoordinateOneKernel_sub_complementOuterMoment_zero
        halpha i
    simpa [mul_assoc] using ((hprime.mul hkernel).mul hratio)
  have hsum : Tendsto (fun N : ℕ ↦
      ∑ i : BoundedGaps.engelsmaTuple,
        ((((affinePrimeIntervalCount (c i) N / c i) / (N : ℝ)) *
            Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)) *
          (((BoundedGaps.Maynard.engelsmaMaynardS2CoordinateOneYDiagonal
                  alpha N i -
                BoundedGaps.Maynard.engelsmaMaynardS2RestrictedCrossCorrection
                  alpha N i) -
              BoundedGaps.Maynard.preSieveSingularSeries
                  (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) ^ 2 *
                BoundedGaps.Maynard.engelsmaS2CoordinateFiberGoodComplementOuterMoment
                  (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
                  (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) i) /
            (BoundedGaps.Maynard.preSieveSingularSeries
                (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) *
              Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)) ^ 106) *
          (Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) /
            Real.log (BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N)) ^ 105))
      atTop (nhds 0) := by
    have hs : Tendsto (fun N : ℕ ↦
        ∑ i : BoundedGaps.engelsmaTuple,
          ((((affinePrimeIntervalCount (c i) N / c i) / (N : ℝ)) *
              Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)) *
            (((BoundedGaps.Maynard.engelsmaMaynardS2CoordinateOneYDiagonal
                    alpha N i -
                  BoundedGaps.Maynard.engelsmaMaynardS2RestrictedCrossCorrection
                    alpha N i) -
                BoundedGaps.Maynard.preSieveSingularSeries
                    (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) ^ 2 *
                  BoundedGaps.Maynard.engelsmaS2CoordinateFiberGoodComplementOuterMoment
                    (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
                    (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) i) /
              (BoundedGaps.Maynard.preSieveSingularSeries
                  (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) *
                Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)) ^ 106) *
            (Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) /
              Real.log (BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N)) ^ 105))
        atTop (nhds (∑ _i : BoundedGaps.engelsmaTuple, (0 : ℝ))) := by
      apply tendsto_finsetSum
      intro i hi
      exact hterm i
    simpa using hs
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop 1,
    BoundedGaps.Maynard.eventually_one_lt_engelsmaMaynardRadius halpha,
    eventually_ge_atTop 3] with N hN hR hN3
  have hRreal : 1 < BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N := by
    unfold BoundedGaps.Maynard.engelsmaMaynardRealRadius
      BoundedGaps.Maynard.maynardRealCutoff
    apply Real.one_lt_rpow
    · exact_mod_cast (show 1 < N - 1 by omega)
    · exact halpha
  exact (affineMaynardS2Main_sub_goodComplementMain_div_scale_eq
    (c := c) (show 0 < N by omega) hR hRreal).symm

theorem tendsto_affineMaynardS2Main_div_scale_of_pnt
    {c : BoundedGaps.engelsmaTuple → ℕ} (hc : ∀ i, 0 < c i)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hpnt : Tendsto
      (fun n : ℕ ↦
        (BoundedGaps.Maynard.primeCountTotal n : ℝ) *
          Real.log (n : ℝ) / (n : ℝ)) atTop (nhds 1)) :
    Tendsto (fun N : ℕ ↦
      affineMaynardS2Main c alpha N /
        BoundedGaps.Maynard.engelsmaMaynardScale alpha N)
      atTop (nhds (alpha *
        (∑ i : Fin 105, BoundedGaps.Maynard.maynardJ 105 i
          BoundedGaps.Maynard.smallKCandidate))) := by
  have herr := tendsto_affineMaynardS2Main_sub_goodComplementMain_div_scale_zero
    hc halpha hpnt
  have hmain := tendsto_affineMaynardS2GoodComplementMain_div_scale_of_pnt
    hc halpha hpnt
  have hadd := herr.add hmain
  have hface := BoundedGaps.Maynard.sum_engelsmaS2GoodOuterFaceLimit_eq_maynardNumerator
  have hadd' : Tendsto (fun N : ℕ ↦
      (affineMaynardS2Main c alpha N -
        affineMaynardS2GoodComplementMain c alpha N) /
          BoundedGaps.Maynard.engelsmaMaynardScale alpha N +
        affineMaynardS2GoodComplementMain c alpha N /
          BoundedGaps.Maynard.engelsmaMaynardScale alpha N)
      atTop (nhds (alpha *
        (∑ i : Fin 105, BoundedGaps.Maynard.maynardJ 105 i
          BoundedGaps.Maynard.smallKCandidate))) := by
    simpa [hface] using hadd
  apply hadd'.congr'
  filter_upwards [] with N
  ring

/-! ## Reduced affine CRT residues -/

open scoped ArithmeticFunction.omega

theorem primeLevelWitness_sum_tauPow_mul_scaled_maxProgressionDiscrepancy
    {theta A C : ℝ} {X₀ x d Q a : ℕ}
    (hw : BoundedGaps.Maynard.PrimeLevelWitness theta A C X₀)
    (hx : X₀ ≤ x) (ha : 0 < a) (S : Finset ℕ)
    (hSQ : S ⊆ Finset.Icc 1 Q)
    (hsq : ∀ q ∈ S, Squarefree q)
    (hsize : a * Q ≤ x + 1)
    (hcut : S.image (fun q ↦ a * q) ⊆
      Finset.Icc 1 (BoundedGaps.Maynard.modulusCutoff theta x)) :
    (∑ q ∈ S, (((d ^ ω q : ℕ) : ℝ) *
        BoundedGaps.Maynard.maxProgressionDiscrepancy x (a * q))) ≤
      Real.sqrt
          ((3 : ℝ) * ((x + 1 : ℕ) : ℝ) *
            (1 + Real.log Q) ^ (2 * d ^ 2)) *
        Real.sqrt
          (C * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) A) := by
  have hpoint : ∀ q ∈ S,
      BoundedGaps.Maynard.maxProgressionDiscrepancy x (a * q) ≤
        ((3 : ℝ) * ((x + 1 : ℕ) : ℝ)) / (Nat.totient q : ℝ) := by
    intro q hq
    have hqData := Finset.mem_Icc.mp (hSQ hq)
    have hqpos : 0 < q := zero_lt_one.trans_le hqData.1
    have haqpos : 0 < a * q := mul_pos ha hqpos
    have haqsize : a * q ≤ x + 1 :=
      (Nat.mul_le_mul_left a hqData.2).trans hsize
    have htriv :=
      BoundedGaps.Maynard.maxProgressionDiscrepancy_le_three_mul_div
        haqpos haqsize
    have hphiPos : (0 : ℝ) < Nat.totient q := by
      exact_mod_cast Nat.totient_pos.mpr hqpos
    have hphiLeNat : Nat.totient q ≤ Nat.totient (a * q) :=
      Nat.le_of_dvd (Nat.totient_pos.mpr haqpos)
        (Nat.totient_dvd_of_dvd (dvd_mul_left q a))
    have hphiLe : (Nat.totient q : ℝ) ≤ Nat.totient (a * q) := by
      exact_mod_cast hphiLeNat
    exact htriv.trans (div_le_div₀ (by positivity) le_rfl hphiPos hphiLe)
  have hweighted := BoundedGaps.Maynard.sum_weight_mul_le_sqrt_of_pointwise_div S
    (fun q ↦ ((d ^ ω q : ℕ) : ℝ))
    (fun q ↦ BoundedGaps.Maynard.maxProgressionDiscrepancy x (a * q))
    (fun q ↦ (Nat.totient q : ℝ))
    ((3 : ℝ) * ((x + 1 : ℕ) : ℝ))
    (fun q _ ↦ BoundedGaps.Maynard.maxProgressionDiscrepancy_nonneg x (a * q))
    hpoint
  have htau := BoundedGaps.Maynard.sum_tauPow_sq_div_totient_le_one_add_log
    d Q S hSQ hsq
  have hlevel := hw.sum_maxProgressionDiscrepancy_subset hx
    (S.image (fun q ↦ a * q)) hcut
  have himage :
      (∑ m ∈ S.image (fun q ↦ a * q),
          BoundedGaps.Maynard.maxProgressionDiscrepancy x m) =
        ∑ q ∈ S,
          BoundedGaps.Maynard.maxProgressionDiscrepancy x (a * q) := by
    exact Finset.sum_image (f :=
      BoundedGaps.Maynard.maxProgressionDiscrepancy x)
      (fun _ _ _ _ h ↦ Nat.eq_of_mul_eq_mul_left ha h)
  rw [himage] at hlevel
  calc
    (∑ q ∈ S, (((d ^ ω q : ℕ) : ℝ) *
        BoundedGaps.Maynard.maxProgressionDiscrepancy x (a * q))) ≤
        Real.sqrt
          (((3 : ℝ) * ((x + 1 : ℕ) : ℝ)) *
            ∑ q ∈ S, (((d ^ ω q : ℕ) : ℝ) ^ 2) /
              (Nat.totient q : ℝ)) *
          Real.sqrt (∑ q ∈ S,
            BoundedGaps.Maynard.maxProgressionDiscrepancy x (a * q)) := hweighted
    _ ≤ Real.sqrt
          ((3 : ℝ) * ((x + 1 : ℕ) : ℝ) *
            (1 + Real.log Q) ^ (2 * d ^ 2)) *
          Real.sqrt (∑ q ∈ S,
            BoundedGaps.Maynard.maxProgressionDiscrepancy x (a * q)) := by
      apply mul_le_mul_of_nonneg_right
      · apply Real.sqrt_le_sqrt
        exact mul_le_mul_of_nonneg_left htau (by positivity)
      · positivity
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left
      · exact Real.sqrt_le_sqrt hlevel
      · positivity

theorem primeLevelWitness_sum_scaled_maxProgressionDiscrepancy_compatiblePairShift_tau
    {theta A C : ℝ} {X₀ x : ℕ}
    (hw : BoundedGaps.Maynard.PrimeLevelWitness theta A C X₀)
    {H : Finset ℕ} {D : Finset (H → ℕ)} {R W Q a : ℕ}
    (hx : X₀ ≤ x) (hH : H.Nonempty) (hW : Squarefree W)
    (hD : ∀ d ∈ D,
      BoundedGaps.Maynard.IsMaynardDivisorTuple H R W d)
    (ha : 0 < a)
    (hSQ : (BoundedGaps.Maynard.compatiblePairShiftIndex H D).image
      (BoundedGaps.Maynard.compatiblePairShiftModulus H W) ⊆
        Finset.Icc 1 Q)
    (hsize : a * Q ≤ x + 1)
    (hcut : a * Q ≤ BoundedGaps.Maynard.modulusCutoff theta x) :
    (∑ i ∈ BoundedGaps.Maynard.compatiblePairShiftIndex H D,
        BoundedGaps.Maynard.maxProgressionDiscrepancy x
          (a * BoundedGaps.Maynard.compatiblePairShiftModulus H W i)) ≤
      BoundedGaps.Maynard.tauIndexedEndpointEnvelope H Q C A x := by
  let S := (BoundedGaps.Maynard.compatiblePairShiftIndex H D).image
    (BoundedGaps.Maynard.compatiblePairShiftModulus H W)
  let d := 3 * Fintype.card H
  have hWpos : 0 < W := Nat.pos_of_ne_zero hW.ne_zero
  have hsq : ∀ q ∈ S, Squarefree q := by
    intro q hq
    exact BoundedGaps.Maynard.squarefree_of_mem_compatiblePairShiftModulus_image
      hW hD hq
  have hscaledCut : S.image (fun q ↦ a * q) ⊆
      Finset.Icc 1 (BoundedGaps.Maynard.modulusCutoff theta x) := by
    intro m hm
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hm
    have hqData := Finset.mem_Icc.mp (hSQ hq)
    exact Finset.mem_Icc.mpr
      ⟨mul_pos ha (zero_lt_one.trans_le hqData.1),
        (Nat.mul_le_mul_left a hqData.2).trans hcut⟩
  have hweighted := primeLevelWitness_sum_tauPow_mul_scaled_maxProgressionDiscrepancy
    (d := d) hw hx ha S hSQ hsq hsize hscaledCut
  calc
    (∑ i ∈ BoundedGaps.Maynard.compatiblePairShiftIndex H D,
        BoundedGaps.Maynard.maxProgressionDiscrepancy x
          (a * BoundedGaps.Maynard.compatiblePairShiftModulus H W i)) =
      ∑ q ∈ S,
        (BoundedGaps.Maynard.modulusFiberCard
          (BoundedGaps.Maynard.compatiblePairShiftIndex H D)
          (BoundedGaps.Maynard.compatiblePairShiftModulus H W) q : ℝ) *
          BoundedGaps.Maynard.maxProgressionDiscrepancy x (a * q) := by
      simpa [S] using
        (BoundedGaps.Maynard.sum_comp_eq_sum_modulusFiberCard
          (BoundedGaps.Maynard.compatiblePairShiftIndex H D)
          (BoundedGaps.Maynard.compatiblePairShiftModulus H W)
          (fun q ↦ BoundedGaps.Maynard.maxProgressionDiscrepancy x (a * q)))
    _ ≤
        ∑ q ∈ S,
          ((((d ^ ω q) * Fintype.card H : ℕ) : ℝ) *
            BoundedGaps.Maynard.maxProgressionDiscrepancy x (a * q)) := by
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast BoundedGaps.Maynard.modulusFiberCard_le_tauPow
          hH hWpos hD (hsq q hq)
          (BoundedGaps.Maynard.W_dvd_of_mem_compatiblePairShiftModulus_image hq)
      · exact BoundedGaps.Maynard.maxProgressionDiscrepancy_nonneg x (a * q)
    _ = (Fintype.card H : ℝ) *
        ∑ q ∈ S, (((d ^ ω q : ℕ) : ℝ) *
          BoundedGaps.Maynard.maxProgressionDiscrepancy x (a * q)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      push_cast
      ring
    _ ≤ (Fintype.card H : ℝ) *
        (Real.sqrt
            ((3 : ℝ) * ((x + 1 : ℕ) : ℝ) *
              (1 + Real.log Q) ^ (2 * d ^ 2)) *
          Real.sqrt
            (C * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) A)) := by
      exact mul_le_mul_of_nonneg_left hweighted (by positivity)
    _ = BoundedGaps.Maynard.tauIndexedEndpointEnvelope H Q C A x := by
      rfl

theorem affineDivisorPairCrtResidue_coprime
    {c : BoundedGaps.engelsmaTuple → ℕ} {R W : ℕ}
    {d e : BoundedGaps.engelsmaTuple → ℕ}
    (hW : 0 < W)
    (hc : ∀ i, 0 < c i)
    (hcoverCoeff : CoefficientPrimesCovered c W)
    (hcoverDiff : CoefficientDifferencesCovered c W)
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple
      BoundedGaps.engelsmaTuple R W d)
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple
      BoundedGaps.engelsmaTuple R W e)
    (hcross : BoundedGaps.Maynard.IsCrossCoordinateCoprime
      BoundedGaps.engelsmaTuple d e)
    (i : BoundedGaps.engelsmaTuple) (hdi : d i = 1) (hei : e i = 1) :
    Nat.Coprime
      (c i * pairCrtResidue c R W d e hd he hcross +
        c i * BoundedGaps.Maynard.divisorPairModulus
          BoundedGaps.engelsmaTuple W d e - 1)
      (c i * BoundedGaps.Maynard.divisorPairModulus
        BoundedGaps.engelsmaTuple W d e) := by
  classical
  let r := pairCrtResidue c R W d e hd he hcross
  let q := BoundedGaps.Maynard.divisorPairModulus
    BoundedGaps.engelsmaTuple W d e
  let s := c i * r + c i * q - 1
  have hqpos : 0 < q := by
    dsimp [q]
    exact BoundedGaps.Maynard.divisorPairModulus_pos
      hW hd he
  have htotal : s + 1 = c i * r + c i * q := by
    dsimp [s]
    have : 1 ≤ c i * r + c i * q := by
      have : 0 < c i * q := mul_pos (hc i) hqpos
      omega
    exact Nat.sub_add_cancel this
  have hrCrt : r ≡ pairCrtResidue c R W d e hd he hcross [MOD q] :=
    Nat.ModEq.refl _
  obtain ⟨hrW, hrPair⟩ :=
    (modEq_pairCrtResidue_iff hcoverCoeff hd he hcross r).mp hrCrt
  have hWq : W ∣ q := by
    dsimp [q]
    exact dvd_mul_right W _
  have hWtotal : W ∣ s + 1 := by
    rw [htotal]
    exact dvd_add (dvd_mul_of_dvd_right
      (Nat.modEq_zero_iff_dvd.mp hrW) (c i))
      (dvd_mul_of_dvd_right hWq (c i))
  have hcopSucc : Nat.Coprime s (s + 1) := by
    simpa [Nat.add_comm] using Nat.coprime_one_right s
  have hcopW : Nat.Coprime s W :=
    hcopSucc.coprime_dvd_right hWtotal
  have hcopProd : Nat.Coprime s
      (∏ j : BoundedGaps.engelsmaTuple,
        BoundedGaps.Maynard.divisorTupleLcm
          BoundedGaps.engelsmaTuple d e j) := by
    apply Nat.Coprime.prod_right
    intro j hj
    by_cases hji : j = i
    · subst j
      simp [BoundedGaps.Maynard.divisorTupleLcm, hdi, hei]
    · by_contra hnot
      obtain ⟨p, hp, hps, hplcm⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
      have hpde : p ∣ d j ∨ p ∣ e j := hp.dvd_or_dvd_of_dvd_lcm hplcm
      have hpq : p ∣ q := by
        dsimp [q, BoundedGaps.Maynard.divisorPairModulus]
        apply dvd_mul_of_dvd_right
        exact hplcm.trans (Finset.dvd_prod_of_mem
          (fun k : BoundedGaps.engelsmaTuple ↦
            BoundedGaps.Maynard.divisorTupleLcm
              BoundedGaps.engelsmaTuple d e k) (Finset.mem_univ j))
      have hpar : c i * r ≡ 1 [MOD p] := by
        have hs0 : s ≡ 0 [MOD p] := hps.modEq_zero_nat
        have hq0 : c i * q ≡ 0 [MOD p] :=
          (dvd_mul_of_dvd_right hpq (c i)).modEq_zero_nat
        have hsum : c i * r + c i * q ≡ 1 [MOD p] := by
          rw [← htotal]
          simpa using hs0.add_right 1
        have hone : 1 ≡ 1 + c i * q [MOD p] := by
          simpa using (hq0.add_left 1).symm
        exact Nat.ModEq.add_right_cancel' (c i * q)
          (hsum.trans hone)
      have hpjr : c j * r ≡ 1 [MOD p] := by
        rcases hpde with hpj | hpj
        · exact (hrPair.1 j).of_dvd hpj
        · exact (hrPair.2 j).of_dvd hpj
      have hcoeff : c j ≡ c i [MOD p] := by
        have hi' := hpar.mul_left (c j)
        have hj' := hpjr.mul_left (c i)
        simpa [mul_assoc, mul_comm, mul_left_comm] using
          hi'.symm.trans (by
            simpa [mul_assoc, mul_comm, mul_left_comm] using hj')
      have hpdist : p ∣ Nat.dist (c i) (c j) :=
        dvd_dist_of_modEq hcoeff.symm
      have hpW : p ∣ W := hcoverDiff i j (Ne.symm hji) p hp hpdist
      have hpcop : Nat.Coprime p W := hcopW.coprime_dvd_left hps
      exact (hp.coprime_iff_not_dvd.mp hpcop) hpW
  have hcopq : Nat.Coprime s q := by
    dsimp [q, BoundedGaps.Maynard.divisorPairModulus]
    exact hcopW.mul_right hcopProd
  have hatotal : c i ∣ s + 1 := by
    rw [htotal]
    exact dvd_add (dvd_mul_right _ _) (dvd_mul_right _ _)
  have hcopa : Nat.Coprime s (c i) :=
    hcopSucc.coprime_dvd_right hatotal
  simpa [s, q] using hcopa.mul_right hcopq

theorem affineDivisorPairCrtResidue_mod_mem_coprimeResidues
    {c : BoundedGaps.engelsmaTuple → ℕ} {R W : ℕ}
    {d e : BoundedGaps.engelsmaTuple → ℕ}
    (hW : 0 < W)
    (hc : ∀ i, 0 < c i)
    (hcoverCoeff : CoefficientPrimesCovered c W)
    (hcoverDiff : CoefficientDifferencesCovered c W)
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple
      BoundedGaps.engelsmaTuple R W d)
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple
      BoundedGaps.engelsmaTuple R W e)
    (hcross : BoundedGaps.Maynard.IsCrossCoordinateCoprime
      BoundedGaps.engelsmaTuple d e)
    (i : BoundedGaps.engelsmaTuple) (hdi : d i = 1) (hei : e i = 1) :
    (c i * pairCrtResidue c R W d e hd he hcross +
        c i * BoundedGaps.Maynard.divisorPairModulus
          BoundedGaps.engelsmaTuple W d e - 1) %
        (c i * BoundedGaps.Maynard.divisorPairModulus
          BoundedGaps.engelsmaTuple W d e) ∈
      BoundedGaps.Maynard.coprimeResidues
        (c i * BoundedGaps.Maynard.divisorPairModulus
          BoundedGaps.engelsmaTuple W d e) := by
  have hq := BoundedGaps.Maynard.divisorPairModulus_pos
    hW hd he
  have hmodpos : 0 < c i * BoundedGaps.Maynard.divisorPairModulus
      BoundedGaps.engelsmaTuple W d e := mul_pos (hc i) hq
  have hcop := affineDivisorPairCrtResidue_coprime
    hW hc hcoverCoeff hcoverDiff hd he hcross i hdi hei
  simp only [BoundedGaps.Maynard.coprimeResidues,
    Finset.mem_filter, Finset.mem_range]
  exact ⟨Nat.mod_lt _ hmodpos,
    by simpa [Nat.coprime_iff_gcd_eq_one] using hcop⟩

theorem affinePrimeProgressionError_le_global_max
    {c : BoundedGaps.engelsmaTuple → ℕ} {R W N : ℕ}
    {d e : BoundedGaps.engelsmaTuple → ℕ}
    (hW : 0 < W) (hc : ∀ i, 0 < c i)
    (hcoverCoeff : CoefficientPrimesCovered c W)
    (hcoverDiff : CoefficientDifferencesCovered c W)
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple
      BoundedGaps.engelsmaTuple R W d)
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple
      BoundedGaps.engelsmaTuple R W e)
    (hcross : BoundedGaps.Maynard.IsCrossCoordinateCoprime
      BoundedGaps.engelsmaTuple d e)
    (i : BoundedGaps.engelsmaTuple) (hdi : d i = 1) (hei : e i = 1)
    (hN : 1 < N) :
    |affinePrimeProgressionError (c i) N
        (BoundedGaps.Maynard.divisorPairModulus
          BoundedGaps.engelsmaTuple W d e)
        (pairCrtResidue c R W d e hd he hcross)| ≤
      BoundedGaps.Maynard.maxProgressionDiscrepancy (c i * (2 * N) - 2)
          (c i * BoundedGaps.Maynard.divisorPairModulus
            BoundedGaps.engelsmaTuple W d e) +
        BoundedGaps.Maynard.maxProgressionDiscrepancy (c i * N - 2)
          (c i * BoundedGaps.Maynard.divisorPairModulus
            BoundedGaps.engelsmaTuple W d e) := by
  let q := BoundedGaps.Maynard.divisorPairModulus
    BoundedGaps.engelsmaTuple W d e
  let r := pairCrtResidue c R W d e hd he hcross
  let a := c i * r + c i * q - 1
  have hq : 0 < q := BoundedGaps.Maynard.divisorPairModulus_pos hW hd he
  have haq : 0 < c i * q := mul_pos (hc i) hq
  have hred : a % (c i * q) ∈
      BoundedGaps.Maynard.coprimeResidues (c i * q) := by
    dsimp [a, q, r]
    exact affineDivisorPairCrtResidue_mod_mem_coprimeResidues
      hW hc hcoverCoeff hcoverDiff hd he hcross i hdi hei
  have hreduce (x : ℕ) :
      BoundedGaps.Maynard.progressionDiscrepancy x (c i * q) a =
        BoundedGaps.Maynard.progressionDiscrepancy x (c i * q)
          (a % (c i * q)) := by
    unfold BoundedGaps.Maynard.progressionDiscrepancy
      BoundedGaps.Maynard.primeCountUpTo
    simp only [Nat.mod_mod]
  calc
    |affinePrimeProgressionError (c i) N q r| ≤
        BoundedGaps.Maynard.progressionDiscrepancy (c i * (2 * N) - 2)
            (c i * q) a +
          BoundedGaps.Maynard.progressionDiscrepancy (c i * N - 2)
            (c i * q) a :=
      affinePrimeProgressionError_le_global_sum (hc i) hN hq
    _ = BoundedGaps.Maynard.progressionDiscrepancy (c i * (2 * N) - 2)
            (c i * q) (a % (c i * q)) +
          BoundedGaps.Maynard.progressionDiscrepancy (c i * N - 2)
            (c i * q) (a % (c i * q)) := by
      rw [hreduce, hreduce]
    _ ≤ BoundedGaps.Maynard.maxProgressionDiscrepancy (c i * (2 * N) - 2)
            (c i * q) +
          BoundedGaps.Maynard.maxProgressionDiscrepancy (c i * N - 2)
            (c i * q) :=
      add_le_add
        (BoundedGaps.Maynard.progressionDiscrepancy_le_max haq hred)
        (BoundedGaps.Maynard.progressionDiscrepancy_le_max haq hred)

noncomputable def affineCompatiblePairCrtResidue
    (c : BoundedGaps.engelsmaTuple → ℕ)
    (D : Finset (BoundedGaps.engelsmaTuple → ℕ)) (R W : ℕ)
    (hD : ∀ d ∈ D, BoundedGaps.Maynard.IsMaynardDivisorTuple
      BoundedGaps.engelsmaTuple R W d)
    (i : (((BoundedGaps.engelsmaTuple → ℕ) ×
      (BoundedGaps.engelsmaTuple → ℕ)) × BoundedGaps.engelsmaTuple)) : ℕ :=
  if hi : i ∈ BoundedGaps.Maynard.compatiblePairShiftIndex
      BoundedGaps.engelsmaTuple D then
    pairCrtResidue c R W i.1.1 i.1.2
      (hD i.1.1 (BoundedGaps.Maynard.compatiblePairShiftIndex_data hi).1)
      (hD i.1.2 (BoundedGaps.Maynard.compatiblePairShiftIndex_data hi).2.1)
      (BoundedGaps.Maynard.compatiblePairShiftIndex_data hi).2.2.1
  else 0

def affineCompatiblePairRestrictedAbsoluteErrorOuter
    (c : BoundedGaps.engelsmaTuple → ℕ)
    (D : Finset (BoundedGaps.engelsmaTuple → ℕ)) (R W N : ℕ)
    (coeff : (BoundedGaps.engelsmaTuple → ℕ) → ℝ)
    (hD : ∀ d ∈ D, BoundedGaps.Maynard.IsMaynardDivisorTuple
      BoundedGaps.engelsmaTuple R W d) : ℝ :=
  ∑ d : D,
    ∑ e : D.filter (fun e : BoundedGaps.engelsmaTuple → ℕ ↦
      BoundedGaps.Maynard.IsCrossCoordinateCoprime
        BoundedGaps.engelsmaTuple d.1 e),
      ∑ i : BoundedGaps.engelsmaTuple,
        if d.1 i = 1 ∧ e.1 i = 1 then
          |coeff d.1 * coeff e.1| *
            |affinePrimeProgressionError (c i) N
              (BoundedGaps.Maynard.divisorPairModulus
                BoundedGaps.engelsmaTuple W d.1 e.1)
              (affineCompatiblePairCrtResidue c D R W hD
                ((d.1, e.1), i))|
        else 0

def affineCompatiblePairShiftWeightedErrorSum
    (c : BoundedGaps.engelsmaTuple → ℕ)
    (D : Finset (BoundedGaps.engelsmaTuple → ℕ)) (R W N : ℕ)
    (coeff : (BoundedGaps.engelsmaTuple → ℕ) → ℝ)
    (hD : ∀ d ∈ D, BoundedGaps.Maynard.IsMaynardDivisorTuple
      BoundedGaps.engelsmaTuple R W d) : ℝ :=
  ∑ i ∈ BoundedGaps.Maynard.compatiblePairShiftIndex
      BoundedGaps.engelsmaTuple D,
    |coeff i.1.1 * coeff i.1.2| *
      |affinePrimeProgressionError (c i.2) N
        (BoundedGaps.Maynard.compatiblePairShiftModulus
          BoundedGaps.engelsmaTuple W i)
        (affineCompatiblePairCrtResidue c D R W hD i)|

theorem abs_affineCompatiblePairRestrictedErrorOuter_le_absolute
    {c : BoundedGaps.engelsmaTuple → ℕ}
    {D : Finset (BoundedGaps.engelsmaTuple → ℕ)} {R W N : ℕ}
    {coeff : (BoundedGaps.engelsmaTuple → ℕ) → ℝ}
    (hD : ∀ d ∈ D, BoundedGaps.Maynard.IsMaynardDivisorTuple
      BoundedGaps.engelsmaTuple R W d) :
    |affineCompatiblePairRestrictedErrorOuter c D R W N coeff hD| ≤
      affineCompatiblePairRestrictedAbsoluteErrorOuter c D R W N coeff hD := by
  classical
  unfold affineCompatiblePairRestrictedErrorOuter
    affineCompatiblePairRestrictedAbsoluteErrorOuter
  calc
    |∑ d : D,
        ∑ e : D.filter (fun e : BoundedGaps.engelsmaTuple → ℕ ↦
          BoundedGaps.Maynard.IsCrossCoordinateCoprime
            BoundedGaps.engelsmaTuple d.1 e),
          ∑ i : BoundedGaps.engelsmaTuple,
            if d.1 i = 1 ∧ e.1 i = 1 then
              affinePrimeProgressionError (c i) N
                (BoundedGaps.Maynard.divisorPairModulus
                  BoundedGaps.engelsmaTuple W d.1 e.1)
                (pairCrtResidue c R W d.1 e.1
                  (hD d.1 d.2)
                  (hD e.1 (Finset.mem_filter.mp e.2).1)
                  (Finset.mem_filter.mp e.2).2) *
                (coeff d.1 * coeff e.1)
            else 0| ≤
        ∑ d : D,
          |∑ e : D.filter (fun e : BoundedGaps.engelsmaTuple → ℕ ↦
            BoundedGaps.Maynard.IsCrossCoordinateCoprime
              BoundedGaps.engelsmaTuple d.1 e),
            ∑ i : BoundedGaps.engelsmaTuple,
              if d.1 i = 1 ∧ e.1 i = 1 then
                affinePrimeProgressionError (c i) N
                  (BoundedGaps.Maynard.divisorPairModulus
                    BoundedGaps.engelsmaTuple W d.1 e.1)
                  (pairCrtResidue c R W d.1 e.1
                    (hD d.1 d.2)
                    (hD e.1 (Finset.mem_filter.mp e.2).1)
                    (Finset.mem_filter.mp e.2).2) *
                  (coeff d.1 * coeff e.1)
              else 0| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d : D,
        ∑ e : D.filter (fun e : BoundedGaps.engelsmaTuple → ℕ ↦
          BoundedGaps.Maynard.IsCrossCoordinateCoprime
            BoundedGaps.engelsmaTuple d.1 e),
          |∑ i : BoundedGaps.engelsmaTuple,
            if d.1 i = 1 ∧ e.1 i = 1 then
              affinePrimeProgressionError (c i) N
                (BoundedGaps.Maynard.divisorPairModulus
                  BoundedGaps.engelsmaTuple W d.1 e.1)
                (pairCrtResidue c R W d.1 e.1
                  (hD d.1 d.2)
                  (hD e.1 (Finset.mem_filter.mp e.2).1)
                  (Finset.mem_filter.mp e.2).2) *
                (coeff d.1 * coeff e.1)
            else 0| := by
      apply Finset.sum_le_sum
      intro d hd
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d : D,
        ∑ e : D.filter (fun e : BoundedGaps.engelsmaTuple → ℕ ↦
          BoundedGaps.Maynard.IsCrossCoordinateCoprime
            BoundedGaps.engelsmaTuple d.1 e),
          ∑ i : BoundedGaps.engelsmaTuple,
            |if d.1 i = 1 ∧ e.1 i = 1 then
              affinePrimeProgressionError (c i) N
                (BoundedGaps.Maynard.divisorPairModulus
                  BoundedGaps.engelsmaTuple W d.1 e.1)
                (pairCrtResidue c R W d.1 e.1
                  (hD d.1 d.2)
                  (hD e.1 (Finset.mem_filter.mp e.2).1)
                  (Finset.mem_filter.mp e.2).2) *
                (coeff d.1 * coeff e.1)
            else 0| := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro e he
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ d : D,
        ∑ e : D.filter (fun e : BoundedGaps.engelsmaTuple → ℕ ↦
          BoundedGaps.Maynard.IsCrossCoordinateCoprime
            BoundedGaps.engelsmaTuple d.1 e),
          ∑ i : BoundedGaps.engelsmaTuple,
            if d.1 i = 1 ∧ e.1 i = 1 then
              |coeff d.1 * coeff e.1| *
                |affinePrimeProgressionError (c i) N
                  (BoundedGaps.Maynard.divisorPairModulus
                    BoundedGaps.engelsmaTuple W d.1 e.1)
                  (affineCompatiblePairCrtResidue c D R W hD
                    ((d.1, e.1), i))|
            else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hred : d.1 i = 1 ∧ e.1 i = 1
      · have hindex : ((d.1, e.1), i) ∈
            BoundedGaps.Maynard.compatiblePairShiftIndex
              BoundedGaps.engelsmaTuple D := by
          unfold BoundedGaps.Maynard.compatiblePairShiftIndex
          apply Finset.mem_filter.mpr
          refine ⟨?_, hred⟩
          apply Finset.mem_product.mpr
          refine ⟨?_, Finset.mem_univ i⟩
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_product.mpr
            ⟨d.2, (Finset.mem_filter.mp e.2).1⟩,
            (Finset.mem_filter.mp e.2).2⟩
        have hresidue :
            affineCompatiblePairCrtResidue c D R W hD ((d.1, e.1), i) =
              pairCrtResidue c R W d.1 e.1
                (hD d.1 d.2)
                (hD e.1 (Finset.mem_filter.mp e.2).1)
                (Finset.mem_filter.mp e.2).2 := by
          unfold affineCompatiblePairCrtResidue
          rw [dif_pos hindex]
        rw [if_pos hred, if_pos hred, hresidue, abs_mul]
        ring
      · simp [hred]

theorem affineCompatiblePairRestrictedAbsoluteErrorOuter_eq_weighted
    {c : BoundedGaps.engelsmaTuple → ℕ}
    {D : Finset (BoundedGaps.engelsmaTuple → ℕ)} {R W N : ℕ}
    {coeff : (BoundedGaps.engelsmaTuple → ℕ) → ℝ}
    (hD : ∀ d ∈ D, BoundedGaps.Maynard.IsMaynardDivisorTuple
      BoundedGaps.engelsmaTuple R W d) :
    affineCompatiblePairRestrictedAbsoluteErrorOuter c D R W N coeff hD =
      affineCompatiblePairShiftWeightedErrorSum c D R W N coeff hD := by
  classical
  unfold affineCompatiblePairRestrictedAbsoluteErrorOuter
    affineCompatiblePairShiftWeightedErrorSum
  rw [BoundedGaps.Maynard.compatiblePairShiftIndex]
  rw [Finset.sum_filter]
  symm
  calc
    (∑ a ∈ (((D ×ˢ D).filter (fun de ↦
          BoundedGaps.Maynard.IsCrossCoordinateCoprime
            BoundedGaps.engelsmaTuple de.1 de.2)).product Finset.univ),
        if a.1.1 a.2 = 1 ∧ a.1.2 a.2 = 1 then
          |coeff a.1.1 * coeff a.1.2| *
            |affinePrimeProgressionError (c a.2) N
              (BoundedGaps.Maynard.compatiblePairShiftModulus
                BoundedGaps.engelsmaTuple W a)
              (affineCompatiblePairCrtResidue c D R W hD a)|
        else 0) =
        ∑ de ∈ (D ×ˢ D).filter (fun de ↦
            BoundedGaps.Maynard.IsCrossCoordinateCoprime
              BoundedGaps.engelsmaTuple de.1 de.2),
          ∑ i : BoundedGaps.engelsmaTuple,
            if de.1 i = 1 ∧ de.2 i = 1 then
              |coeff de.1 * coeff de.2| *
                |affinePrimeProgressionError (c i) N
                  (BoundedGaps.Maynard.compatiblePairShiftModulus
                    BoundedGaps.engelsmaTuple W (de, i))
                  (affineCompatiblePairCrtResidue c D R W hD (de, i))|
            else 0 :=
      Finset.sum_product
        ((D ×ˢ D).filter (fun de ↦
          BoundedGaps.Maynard.IsCrossCoordinateCoprime
            BoundedGaps.engelsmaTuple de.1 de.2)) Finset.univ _
    _ = ∑ de ∈ D ×ˢ D,
        if BoundedGaps.Maynard.IsCrossCoordinateCoprime
            BoundedGaps.engelsmaTuple de.1 de.2 then
          ∑ i : BoundedGaps.engelsmaTuple,
            if de.1 i = 1 ∧ de.2 i = 1 then
              |coeff de.1 * coeff de.2| *
                |affinePrimeProgressionError (c i) N
                  (BoundedGaps.Maynard.compatiblePairShiftModulus
                    BoundedGaps.engelsmaTuple W (de, i))
                  (affineCompatiblePairCrtResidue c D R W hD (de, i))|
            else 0
        else 0 :=
      Finset.sum_filter
        (fun de : (BoundedGaps.engelsmaTuple → ℕ) ×
          (BoundedGaps.engelsmaTuple → ℕ) ↦
          BoundedGaps.Maynard.IsCrossCoordinateCoprime
            BoundedGaps.engelsmaTuple de.1 de.2) _
    _ = ∑ d ∈ D, ∑ e ∈ D,
        if BoundedGaps.Maynard.IsCrossCoordinateCoprime
            BoundedGaps.engelsmaTuple d e then
          ∑ i : BoundedGaps.engelsmaTuple,
            if d i = 1 ∧ e i = 1 then
              |coeff d * coeff e| *
                |affinePrimeProgressionError (c i) N
                  (BoundedGaps.Maynard.compatiblePairShiftModulus
                    BoundedGaps.engelsmaTuple W ((d, e), i))
                  (affineCompatiblePairCrtResidue c D R W hD ((d, e), i))|
            else 0
        else 0 := Finset.sum_product D D _
    _ = ∑ d : D,
        ∑ e : D.filter (fun e : BoundedGaps.engelsmaTuple → ℕ ↦
          BoundedGaps.Maynard.IsCrossCoordinateCoprime
            BoundedGaps.engelsmaTuple d.1 e),
          ∑ i : BoundedGaps.engelsmaTuple,
            if d.1 i = 1 ∧ e.1 i = 1 then
              |coeff d.1 * coeff e.1| *
                |affinePrimeProgressionError (c i) N
                  (BoundedGaps.Maynard.divisorPairModulus
                    BoundedGaps.engelsmaTuple W d.1 e.1)
                  (affineCompatiblePairCrtResidue c D R W hD
                    ((d.1, e.1), i))|
            else 0 := by
      unfold BoundedGaps.Maynard.compatiblePairShiftModulus
      let g : (BoundedGaps.engelsmaTuple → ℕ) →
          (BoundedGaps.engelsmaTuple → ℕ) → ℝ := fun d e ↦
        ∑ i : BoundedGaps.engelsmaTuple,
          if d i = 1 ∧ e i = 1 then
            |coeff d * coeff e| *
              |affinePrimeProgressionError (c i) N
                (BoundedGaps.Maynard.divisorPairModulus
                  BoundedGaps.engelsmaTuple W d e)
                (affineCompatiblePairCrtResidue c D R W hD ((d, e), i))|
          else 0
      change (∑ d ∈ D, ∑ e ∈ D,
          if BoundedGaps.Maynard.IsCrossCoordinateCoprime
              BoundedGaps.engelsmaTuple d e then g d e else 0) =
        ∑ d : D,
          ∑ e : D.filter (fun e : BoundedGaps.engelsmaTuple → ℕ ↦
            BoundedGaps.Maynard.IsCrossCoordinateCoprime
              BoundedGaps.engelsmaTuple d.1 e), g d.1 e.1
      calc
        (∑ d ∈ D, ∑ e ∈ D,
            if BoundedGaps.Maynard.IsCrossCoordinateCoprime
                BoundedGaps.engelsmaTuple d e then g d e else 0) =
          ∑ d ∈ D, ∑ e ∈ D.filter (fun e ↦
            BoundedGaps.Maynard.IsCrossCoordinateCoprime
              BoundedGaps.engelsmaTuple d e), g d e := by
          apply Finset.sum_congr rfl
          intro d hd
          exact (Finset.sum_filter (fun e ↦
            BoundedGaps.Maynard.IsCrossCoordinateCoprime
              BoundedGaps.engelsmaTuple d e) (g d)).symm
        _ = ∑ d ∈ D,
            ∑ e : D.filter (fun e ↦
              BoundedGaps.Maynard.IsCrossCoordinateCoprime
                BoundedGaps.engelsmaTuple d e), g d e.1 := by
          apply Finset.sum_congr rfl
          intro d hd
          exact Finset.sum_subtype
            (D.filter (fun e ↦
              BoundedGaps.Maynard.IsCrossCoordinateCoprime
                BoundedGaps.engelsmaTuple d e))
            (fun _ ↦ Iff.rfl) (g d)
        _ = ∑ d : D,
            ∑ e : D.filter (fun e ↦
              BoundedGaps.Maynard.IsCrossCoordinateCoprime
                BoundedGaps.engelsmaTuple d.1 e), g d.1 e.1 :=
          Finset.sum_subtype D (fun _ ↦ Iff.rfl) _

def affineCompatiblePairShiftEndpointDiscrepancySum
    (c : BoundedGaps.engelsmaTuple → ℕ)
    (D : Finset (BoundedGaps.engelsmaTuple → ℕ)) (W N : ℕ) : ℝ :=
  ∑ i ∈ BoundedGaps.Maynard.compatiblePairShiftIndex
      BoundedGaps.engelsmaTuple D,
    (BoundedGaps.Maynard.maxProgressionDiscrepancy
        (c i.2 * (2 * N) - 2)
        (c i.2 * BoundedGaps.Maynard.compatiblePairShiftModulus
          BoundedGaps.engelsmaTuple W i) +
      BoundedGaps.Maynard.maxProgressionDiscrepancy
        (c i.2 * N - 2)
        (c i.2 * BoundedGaps.Maynard.compatiblePairShiftModulus
          BoundedGaps.engelsmaTuple W i))

theorem affineCompatiblePairShiftWeightedErrorSum_le
    {c : BoundedGaps.engelsmaTuple → ℕ}
    {D : Finset (BoundedGaps.engelsmaTuple → ℕ)} {R W N : ℕ}
    {coeff : (BoundedGaps.engelsmaTuple → ℕ) → ℝ} {L : ℝ}
    (hW : 0 < W) (hc : ∀ i, 0 < c i)
    (hcoverCoeff : CoefficientPrimesCovered c W)
    (hcoverDiff : CoefficientDifferencesCovered c W)
    (hD : ∀ d ∈ D, BoundedGaps.Maynard.IsMaynardDivisorTuple
      BoundedGaps.engelsmaTuple R W d)
    (hN : 1 < N) (hL : 0 ≤ L)
    (hbound : ∀ d ∈ D, |coeff d| ≤ L) :
    affineCompatiblePairShiftWeightedErrorSum c D R W N coeff hD ≤
      L ^ 2 * affineCompatiblePairShiftEndpointDiscrepancySum c D W N := by
  classical
  unfold affineCompatiblePairShiftWeightedErrorSum
    affineCompatiblePairShiftEndpointDiscrepancySum
  calc
    (∑ i ∈ BoundedGaps.Maynard.compatiblePairShiftIndex
        BoundedGaps.engelsmaTuple D,
      |coeff i.1.1 * coeff i.1.2| *
        |affinePrimeProgressionError (c i.2) N
          (BoundedGaps.Maynard.compatiblePairShiftModulus
            BoundedGaps.engelsmaTuple W i)
          (affineCompatiblePairCrtResidue c D R W hD i)|) ≤
      ∑ i ∈ BoundedGaps.Maynard.compatiblePairShiftIndex
          BoundedGaps.engelsmaTuple D,
        L ^ 2 *
          (BoundedGaps.Maynard.maxProgressionDiscrepancy
              (c i.2 * (2 * N) - 2)
              (c i.2 * BoundedGaps.Maynard.compatiblePairShiftModulus
                BoundedGaps.engelsmaTuple W i) +
            BoundedGaps.Maynard.maxProgressionDiscrepancy
              (c i.2 * N - 2)
              (c i.2 * BoundedGaps.Maynard.compatiblePairShiftModulus
                BoundedGaps.engelsmaTuple W i)) := by
      apply Finset.sum_le_sum
      intro i hi
      let hiData := BoundedGaps.Maynard.compatiblePairShiftIndex_data hi
      let hdi := hD i.1.1 hiData.1
      let hei := hD i.1.2 hiData.2.1
      let hcrossi : BoundedGaps.Maynard.IsCrossCoordinateCoprime
          BoundedGaps.engelsmaTuple i.1.1 i.1.2 := hiData.2.2.1
      have hresidue : affineCompatiblePairCrtResidue c D R W hD i =
          pairCrtResidue c R W i.1.1 i.1.2 hdi hei hcrossi := by
        unfold affineCompatiblePairCrtResidue
        rw [dif_pos hi]
      have herror :
          |affinePrimeProgressionError (c i.2) N
            (BoundedGaps.Maynard.compatiblePairShiftModulus
              BoundedGaps.engelsmaTuple W i)
            (affineCompatiblePairCrtResidue c D R W hD i)| ≤
            BoundedGaps.Maynard.maxProgressionDiscrepancy
                (c i.2 * (2 * N) - 2)
                (c i.2 * BoundedGaps.Maynard.compatiblePairShiftModulus
                  BoundedGaps.engelsmaTuple W i) +
              BoundedGaps.Maynard.maxProgressionDiscrepancy
                (c i.2 * N - 2)
                (c i.2 * BoundedGaps.Maynard.compatiblePairShiftModulus
                  BoundedGaps.engelsmaTuple W i) := by
        rw [hresidue]
        exact affinePrimeProgressionError_le_global_max
          hW hc hcoverCoeff hcoverDiff hdi hei hcrossi i.2
            hiData.2.2.2.1 hiData.2.2.2.2 hN
      have hcoef : |coeff i.1.1 * coeff i.1.2| ≤ L ^ 2 := by
        rw [abs_mul]
        calc
          |coeff i.1.1| * |coeff i.1.2| ≤ L * L :=
            mul_le_mul (hbound i.1.1 hiData.1)
              (hbound i.1.2 hiData.2.1) (abs_nonneg _) hL
          _ = L ^ 2 := by ring
      calc
        |coeff i.1.1 * coeff i.1.2| *
            |affinePrimeProgressionError (c i.2) N
              (BoundedGaps.Maynard.compatiblePairShiftModulus
                BoundedGaps.engelsmaTuple W i)
              (affineCompatiblePairCrtResidue c D R W hD i)| ≤
          L ^ 2 *
            |affinePrimeProgressionError (c i.2) N
              (BoundedGaps.Maynard.compatiblePairShiftModulus
                BoundedGaps.engelsmaTuple W i)
              (affineCompatiblePairCrtResidue c D R W hD i)| :=
          mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)
        _ ≤ L ^ 2 * _ := mul_le_mul_of_nonneg_left herror (sq_nonneg L)
    _ = L ^ 2 *
        ∑ i ∈ BoundedGaps.Maynard.compatiblePairShiftIndex
            BoundedGaps.engelsmaTuple D,
          (BoundedGaps.Maynard.maxProgressionDiscrepancy
              (c i.2 * (2 * N) - 2)
              (c i.2 * BoundedGaps.Maynard.compatiblePairShiftModulus
                BoundedGaps.engelsmaTuple W i) +
            BoundedGaps.Maynard.maxProgressionDiscrepancy
              (c i.2 * N - 2)
              (c i.2 * BoundedGaps.Maynard.compatiblePairShiftModulus
                BoundedGaps.engelsmaTuple W i)) := by
      rw [Finset.mul_sum]

theorem affineCompatiblePairShiftEndpointDiscrepancySum_le_coordinate_sum
    (c : BoundedGaps.engelsmaTuple → ℕ)
    (D : Finset (BoundedGaps.engelsmaTuple → ℕ)) (W N : ℕ) :
    affineCompatiblePairShiftEndpointDiscrepancySum c D W N ≤
      (∑ h : BoundedGaps.engelsmaTuple,
        ∑ i ∈ BoundedGaps.Maynard.compatiblePairShiftIndex
            BoundedGaps.engelsmaTuple D,
          BoundedGaps.Maynard.maxProgressionDiscrepancy
            (c h * (2 * N) - 2)
            (c h * BoundedGaps.Maynard.compatiblePairShiftModulus
              BoundedGaps.engelsmaTuple W i)) +
      ∑ h : BoundedGaps.engelsmaTuple,
        ∑ i ∈ BoundedGaps.Maynard.compatiblePairShiftIndex
            BoundedGaps.engelsmaTuple D,
          BoundedGaps.Maynard.maxProgressionDiscrepancy
            (c h * N - 2)
            (c h * BoundedGaps.Maynard.compatiblePairShiftModulus
              BoundedGaps.engelsmaTuple W i) := by
  classical
  unfold affineCompatiblePairShiftEndpointDiscrepancySum
  calc
    (∑ i ∈ BoundedGaps.Maynard.compatiblePairShiftIndex
        BoundedGaps.engelsmaTuple D,
      (BoundedGaps.Maynard.maxProgressionDiscrepancy
          (c i.2 * (2 * N) - 2)
          (c i.2 * BoundedGaps.Maynard.compatiblePairShiftModulus
            BoundedGaps.engelsmaTuple W i) +
        BoundedGaps.Maynard.maxProgressionDiscrepancy
          (c i.2 * N - 2)
          (c i.2 * BoundedGaps.Maynard.compatiblePairShiftModulus
            BoundedGaps.engelsmaTuple W i))) ≤
      ∑ i ∈ BoundedGaps.Maynard.compatiblePairShiftIndex
          BoundedGaps.engelsmaTuple D,
        ((∑ h : BoundedGaps.engelsmaTuple,
          BoundedGaps.Maynard.maxProgressionDiscrepancy
            (c h * (2 * N) - 2)
            (c h * BoundedGaps.Maynard.compatiblePairShiftModulus
              BoundedGaps.engelsmaTuple W i)) +
        ∑ h : BoundedGaps.engelsmaTuple,
          BoundedGaps.Maynard.maxProgressionDiscrepancy
            (c h * N - 2)
            (c h * BoundedGaps.Maynard.compatiblePairShiftModulus
              BoundedGaps.engelsmaTuple W i)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply add_le_add
      · exact Finset.single_le_sum
          (f := fun h : BoundedGaps.engelsmaTuple ↦
            BoundedGaps.Maynard.maxProgressionDiscrepancy
              (c h * (2 * N) - 2)
              (c h * BoundedGaps.Maynard.compatiblePairShiftModulus
                BoundedGaps.engelsmaTuple W i))
          (fun h _ ↦ BoundedGaps.Maynard.maxProgressionDiscrepancy_nonneg _ _)
          (Finset.mem_univ i.2)
      · exact Finset.single_le_sum
          (f := fun h : BoundedGaps.engelsmaTuple ↦
            BoundedGaps.Maynard.maxProgressionDiscrepancy
              (c h * N - 2)
              (c h * BoundedGaps.Maynard.compatiblePairShiftModulus
                BoundedGaps.engelsmaTuple W i))
          (fun h _ ↦ BoundedGaps.Maynard.maxProgressionDiscrepancy_nonneg _ _)
          (Finset.mem_univ i.2)
    _ = _ := by
      rw [Finset.sum_add_distrib]
      apply congrArg₂ (fun x y : ℝ ↦ x + y)
      · exact Finset.sum_comm
      · exact Finset.sum_comm

theorem primeLevelWitness_bound_abs_affineCompatiblePairRestrictedErrorOuter_tau
    {theta A C : ℝ} {X₀ : ℕ}
    (hw : BoundedGaps.Maynard.PrimeLevelWitness theta A C X₀)
    {c : BoundedGaps.engelsmaTuple → ℕ}
    {D : Finset (BoundedGaps.engelsmaTuple → ℕ)} {R W N : ℕ}
    {coeff : (BoundedGaps.engelsmaTuple → ℕ) → ℝ} {L : ℝ}
    (hW : Squarefree W) (hc : ∀ i, 0 < c i)
    (hcoverCoeff : CoefficientPrimesCovered c W)
    (hcoverDiff : CoefficientDifferencesCovered c W)
    (hD : ∀ d ∈ D, BoundedGaps.Maynard.IsMaynardDivisorTuple
      BoundedGaps.engelsmaTuple R W d)
    (hN : 1 < N) (hL : 0 ≤ L)
    (hbound : ∀ d ∈ D, |coeff d| ≤ L)
    (hupper : ∀ i : BoundedGaps.engelsmaTuple,
      X₀ ≤ c i * (2 * N) - 2)
    (hlower : ∀ i : BoundedGaps.engelsmaTuple,
      X₀ ≤ c i * N - 2)
    (hcutUpper : ∀ i : BoundedGaps.engelsmaTuple,
      c i * (W * R * R) ≤ BoundedGaps.Maynard.modulusCutoff theta
        (c i * (2 * N) - 2))
    (hcutLower : ∀ i : BoundedGaps.engelsmaTuple,
      c i * (W * R * R) ≤ BoundedGaps.Maynard.modulusCutoff theta
        (c i * N - 2))
    (hsizeUpper : ∀ i : BoundedGaps.engelsmaTuple,
      c i * (W * R * R) ≤ (c i * (2 * N) - 2) + 1)
    (hsizeLower : ∀ i : BoundedGaps.engelsmaTuple,
      c i * (W * R * R) ≤ (c i * N - 2) + 1) :
    |affineCompatiblePairRestrictedErrorOuter c D R W N coeff hD| ≤
      L ^ 2 *
        ((∑ i : BoundedGaps.engelsmaTuple,
          BoundedGaps.Maynard.tauIndexedEndpointEnvelope
            BoundedGaps.engelsmaTuple (W * R * R) C A
              (c i * (2 * N) - 2)) +
        ∑ i : BoundedGaps.engelsmaTuple,
          BoundedGaps.Maynard.tauIndexedEndpointEnvelope
            BoundedGaps.engelsmaTuple (W * R * R) C A
              (c i * N - 2)) := by
  have hWpos : 0 < W := Nat.pos_of_ne_zero hW.ne_zero
  have hH : BoundedGaps.engelsmaTuple.Nonempty := by
    apply Finset.card_pos.mp
    rw [BoundedGaps.engelsmaTuple_card]
    norm_num
  have hSQ := BoundedGaps.Maynard.compatiblePairShiftModulus_image_subset_radius
    hWpos hD
  have hcoord :
      ((∑ i : BoundedGaps.engelsmaTuple,
        ∑ j ∈ BoundedGaps.Maynard.compatiblePairShiftIndex
            BoundedGaps.engelsmaTuple D,
          BoundedGaps.Maynard.maxProgressionDiscrepancy
            (c i * (2 * N) - 2)
            (c i * BoundedGaps.Maynard.compatiblePairShiftModulus
              BoundedGaps.engelsmaTuple W j)) +
      ∑ i : BoundedGaps.engelsmaTuple,
        ∑ j ∈ BoundedGaps.Maynard.compatiblePairShiftIndex
            BoundedGaps.engelsmaTuple D,
          BoundedGaps.Maynard.maxProgressionDiscrepancy
            (c i * N - 2)
            (c i * BoundedGaps.Maynard.compatiblePairShiftModulus
              BoundedGaps.engelsmaTuple W j)) ≤
      (∑ i : BoundedGaps.engelsmaTuple,
        BoundedGaps.Maynard.tauIndexedEndpointEnvelope
          BoundedGaps.engelsmaTuple (W * R * R) C A
            (c i * (2 * N) - 2)) +
      ∑ i : BoundedGaps.engelsmaTuple,
        BoundedGaps.Maynard.tauIndexedEndpointEnvelope
          BoundedGaps.engelsmaTuple (W * R * R) C A
            (c i * N - 2) := by
    apply add_le_add
    · apply Finset.sum_le_sum
      intro i hi
      exact primeLevelWitness_sum_scaled_maxProgressionDiscrepancy_compatiblePairShift_tau
        (x := c i * (2 * N) - 2) (Q := W * R * R)
        hw (hupper i) hH hW hD (hc i) hSQ (hsizeUpper i) (hcutUpper i)
    · apply Finset.sum_le_sum
      intro i hi
      exact primeLevelWitness_sum_scaled_maxProgressionDiscrepancy_compatiblePairShift_tau
        (x := c i * N - 2) (Q := W * R * R)
        hw (hlower i) hH hW hD (hc i) hSQ (hsizeLower i) (hcutLower i)
  calc
    |affineCompatiblePairRestrictedErrorOuter c D R W N coeff hD| ≤
        affineCompatiblePairRestrictedAbsoluteErrorOuter c D R W N coeff hD :=
      abs_affineCompatiblePairRestrictedErrorOuter_le_absolute hD
    _ = affineCompatiblePairShiftWeightedErrorSum c D R W N coeff hD :=
      affineCompatiblePairRestrictedAbsoluteErrorOuter_eq_weighted hD
    _ ≤ L ^ 2 * affineCompatiblePairShiftEndpointDiscrepancySum c D W N :=
      affineCompatiblePairShiftWeightedErrorSum_le hWpos hc hcoverCoeff
        hcoverDiff hD hN hL hbound
    _ ≤ L ^ 2 *
        ((∑ i : BoundedGaps.engelsmaTuple,
          ∑ j ∈ BoundedGaps.Maynard.compatiblePairShiftIndex
              BoundedGaps.engelsmaTuple D,
            BoundedGaps.Maynard.maxProgressionDiscrepancy
              (c i * (2 * N) - 2)
              (c i * BoundedGaps.Maynard.compatiblePairShiftModulus
                BoundedGaps.engelsmaTuple W j)) +
        ∑ i : BoundedGaps.engelsmaTuple,
          ∑ j ∈ BoundedGaps.Maynard.compatiblePairShiftIndex
              BoundedGaps.engelsmaTuple D,
            BoundedGaps.Maynard.maxProgressionDiscrepancy
              (c i * N - 2)
              (c i * BoundedGaps.Maynard.compatiblePairShiftModulus
                BoundedGaps.engelsmaTuple W j)) :=
      mul_le_mul_of_nonneg_left
        (affineCompatiblePairShiftEndpointDiscrepancySum_le_coordinate_sum
          c D W N) (sq_nonneg L)
    _ ≤ _ := mul_le_mul_of_nonneg_left hcoord (sq_nonneg L)

theorem primeCountUpTo_succ_le_add_one (x q a : ℕ) :
    BoundedGaps.Maynard.primeCountUpTo (x + 1) q a ≤
      BoundedGaps.Maynard.primeCountUpTo x q a + 1 := by
  unfold BoundedGaps.Maynard.primeCountUpTo
  rw [show x + 1 + 1 = (x + 1) + 1 by omega, Finset.range_add_one,
    Finset.filter_insert]
  split_ifs <;> simp_all

theorem primeCountUpTo_mono_succ (x q a : ℕ) :
    BoundedGaps.Maynard.primeCountUpTo x q a ≤
      BoundedGaps.Maynard.primeCountUpTo (x + 1) q a := by
  unfold BoundedGaps.Maynard.primeCountUpTo
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
  exact ⟨by omega, hn.2⟩

theorem primeCountTotal_succ_le_add_one (x : ℕ) :
    BoundedGaps.Maynard.primeCountTotal (x + 1) ≤
      BoundedGaps.Maynard.primeCountTotal x + 1 := by
  unfold BoundedGaps.Maynard.primeCountTotal Nat.primeCounting
    Nat.primeCounting'
  rw [show x + 1 + 1 = (x + 1) + 1 by omega, Nat.count_succ]
  split_ifs <;> omega

theorem primeCountTotal_mono_succ (x : ℕ) :
    BoundedGaps.Maynard.primeCountTotal x ≤
      BoundedGaps.Maynard.primeCountTotal (x + 1) := by
  exact Nat.monotone_primeCounting (Nat.le_succ x)

theorem progressionDiscrepancy_le_succ_add_two
    {x q a : ℕ} (hq : 0 < q) :
    BoundedGaps.Maynard.progressionDiscrepancy x q a ≤
      BoundedGaps.Maynard.progressionDiscrepancy (x + 1) q a + 2 := by
  have hphiNat : 0 < Nat.totient q := Nat.totient_pos.mpr hq
  have hphi : (0 : ℝ) < Nat.totient q := by exact_mod_cast hphiNat
  have hpmono := primeCountUpTo_mono_succ x q a
  have hpstep := primeCountUpTo_succ_le_add_one x q a
  have htmono := primeCountTotal_mono_succ x
  have htstep := primeCountTotal_succ_le_add_one x
  let P : ℝ := BoundedGaps.Maynard.primeCountUpTo x q a
  let P' : ℝ := BoundedGaps.Maynard.primeCountUpTo (x + 1) q a
  let T : ℝ := BoundedGaps.Maynard.primeCountTotal x
  let T' : ℝ := BoundedGaps.Maynard.primeCountTotal (x + 1)
  have hp : 0 ≤ P' - P ∧ P' - P ≤ 1 := by
    constructor <;> dsimp [P, P'] <;> exact_mod_cast (by omega)
  have ht : 0 ≤ T' - T ∧ T' - T ≤ 1 := by
    constructor <;> dsimp [T, T'] <;> exact_mod_cast (by omega)
  have htd : 0 ≤ (T' - T) / (Nat.totient q : ℝ) ∧
      (T' - T) / (Nat.totient q : ℝ) ≤ 1 := by
    constructor
    · exact div_nonneg ht.1 hphi.le
    · apply (div_le_one₀ hphi).2
      have hphiOne : (1 : ℝ) ≤ Nat.totient q := by
        exact_mod_cast (show 1 ≤ Nat.totient q by omega)
      exact ht.2.trans hphiOne
  unfold BoundedGaps.Maynard.progressionDiscrepancy
  change |P - T / (Nat.totient q : ℝ)| ≤
    |P' - T' / (Nat.totient q : ℝ)| + 2
  have hid : P - T / (Nat.totient q : ℝ) =
      (P' - T' / (Nat.totient q : ℝ)) -
        ((P' - P) - (T' - T) / (Nat.totient q : ℝ)) := by ring
  rw [hid]
  calc
    |(P' - T' / (Nat.totient q : ℝ)) -
        ((P' - P) - (T' - T) / (Nat.totient q : ℝ))| ≤
      |P' - T' / (Nat.totient q : ℝ)| +
        |(P' - P) - (T' - T) / (Nat.totient q : ℝ)| := abs_sub _ _
    _ ≤ |P' - T' / (Nat.totient q : ℝ)| + 2 := by
      have hab : |(P' - P) - (T' - T) / (Nat.totient q : ℝ)| ≤ 2 := by
        rw [abs_le]
        constructor <;> linarith [hp.1, hp.2, htd.1, htd.2]
      linarith

theorem maxProgressionDiscrepancy_le_succ_add_two (x q : ℕ) :
    BoundedGaps.Maynard.maxProgressionDiscrepancy x q ≤
      BoundedGaps.Maynard.maxProgressionDiscrepancy (x + 1) q + 2 := by
  by_cases hq : 0 < q
  · unfold BoundedGaps.Maynard.maxProgressionDiscrepancy
    simp only [dif_pos hq]
    apply Finset.sup'_le
    intro a ha
    have hm := BoundedGaps.Maynard.progressionDiscrepancy_le_max
      (x := x + 1) hq ha
    rw [BoundedGaps.Maynard.maxProgressionDiscrepancy, dif_pos hq] at hm
    calc
      BoundedGaps.Maynard.progressionDiscrepancy x q a ≤
          BoundedGaps.Maynard.progressionDiscrepancy (x + 1) q a + 2 :=
        progressionDiscrepancy_le_succ_add_two hq
      _ ≤ _ := add_le_add hm le_rfl
  · have hq0 : q = 0 := by omega
    subst q
    simp [BoundedGaps.Maynard.maxProgressionDiscrepancy]

def affineCompatiblePairShiftRaisedEndpointDiscrepancySum
    (c : BoundedGaps.engelsmaTuple → ℕ)
    (D : Finset (BoundedGaps.engelsmaTuple → ℕ)) (W N : ℕ) : ℝ :=
  ∑ i ∈ BoundedGaps.Maynard.compatiblePairShiftIndex
      BoundedGaps.engelsmaTuple D,
    (BoundedGaps.Maynard.maxProgressionDiscrepancy
        ((c i.2 * (2 * N) - 2) + 1)
        (c i.2 * BoundedGaps.Maynard.compatiblePairShiftModulus
          BoundedGaps.engelsmaTuple W i) +
      BoundedGaps.Maynard.maxProgressionDiscrepancy
        ((c i.2 * N - 2) + 1)
        (c i.2 * BoundedGaps.Maynard.compatiblePairShiftModulus
          BoundedGaps.engelsmaTuple W i))

theorem affineCompatiblePairShiftEndpointDiscrepancySum_le_raised
    (c : BoundedGaps.engelsmaTuple → ℕ)
    (D : Finset (BoundedGaps.engelsmaTuple → ℕ)) (W N : ℕ) :
    affineCompatiblePairShiftEndpointDiscrepancySum c D W N ≤
      affineCompatiblePairShiftRaisedEndpointDiscrepancySum c D W N +
        4 * ((BoundedGaps.Maynard.compatiblePairShiftIndex
          BoundedGaps.engelsmaTuple D).card : ℝ) := by
  classical
  unfold affineCompatiblePairShiftEndpointDiscrepancySum
    affineCompatiblePairShiftRaisedEndpointDiscrepancySum
  calc
    (∑ i ∈ BoundedGaps.Maynard.compatiblePairShiftIndex
        BoundedGaps.engelsmaTuple D,
      (BoundedGaps.Maynard.maxProgressionDiscrepancy
          (c i.2 * (2 * N) - 2)
          (c i.2 * BoundedGaps.Maynard.compatiblePairShiftModulus
            BoundedGaps.engelsmaTuple W i) +
        BoundedGaps.Maynard.maxProgressionDiscrepancy
          (c i.2 * N - 2)
          (c i.2 * BoundedGaps.Maynard.compatiblePairShiftModulus
            BoundedGaps.engelsmaTuple W i))) ≤
      ∑ i ∈ BoundedGaps.Maynard.compatiblePairShiftIndex
          BoundedGaps.engelsmaTuple D,
        ((BoundedGaps.Maynard.maxProgressionDiscrepancy
            ((c i.2 * (2 * N) - 2) + 1)
            (c i.2 * BoundedGaps.Maynard.compatiblePairShiftModulus
              BoundedGaps.engelsmaTuple W i) +
          BoundedGaps.Maynard.maxProgressionDiscrepancy
            ((c i.2 * N - 2) + 1)
            (c i.2 * BoundedGaps.Maynard.compatiblePairShiftModulus
              BoundedGaps.engelsmaTuple W i)) + 4) := by
      apply Finset.sum_le_sum
      intro i hi
      have hu := maxProgressionDiscrepancy_le_succ_add_two
        (c i.2 * (2 * N) - 2)
        (c i.2 * BoundedGaps.Maynard.compatiblePairShiftModulus
          BoundedGaps.engelsmaTuple W i)
      have hl := maxProgressionDiscrepancy_le_succ_add_two
        (c i.2 * N - 2)
        (c i.2 * BoundedGaps.Maynard.compatiblePairShiftModulus
          BoundedGaps.engelsmaTuple W i)
      linarith
    _ = (∑ i ∈ BoundedGaps.Maynard.compatiblePairShiftIndex
          BoundedGaps.engelsmaTuple D,
        (BoundedGaps.Maynard.maxProgressionDiscrepancy
            ((c i.2 * (2 * N) - 2) + 1)
            (c i.2 * BoundedGaps.Maynard.compatiblePairShiftModulus
              BoundedGaps.engelsmaTuple W i) +
          BoundedGaps.Maynard.maxProgressionDiscrepancy
            ((c i.2 * N - 2) + 1)
            (c i.2 * BoundedGaps.Maynard.compatiblePairShiftModulus
              BoundedGaps.engelsmaTuple W i))) +
        4 * ((BoundedGaps.Maynard.compatiblePairShiftIndex
          BoundedGaps.engelsmaTuple D).card : ℝ) := by
      rw [Finset.sum_add_distrib]
      simp [Finset.sum_const, nsmul_eq_mul]
      ring

theorem affineCompatiblePairShiftRaisedEndpointDiscrepancySum_le_coordinate_sum
    (c : BoundedGaps.engelsmaTuple → ℕ)
    (D : Finset (BoundedGaps.engelsmaTuple → ℕ)) (W N : ℕ) :
    affineCompatiblePairShiftRaisedEndpointDiscrepancySum c D W N ≤
      (∑ h : BoundedGaps.engelsmaTuple,
        ∑ i ∈ BoundedGaps.Maynard.compatiblePairShiftIndex
            BoundedGaps.engelsmaTuple D,
          BoundedGaps.Maynard.maxProgressionDiscrepancy
            ((c h * (2 * N) - 2) + 1)
            (c h * BoundedGaps.Maynard.compatiblePairShiftModulus
              BoundedGaps.engelsmaTuple W i)) +
      ∑ h : BoundedGaps.engelsmaTuple,
        ∑ i ∈ BoundedGaps.Maynard.compatiblePairShiftIndex
            BoundedGaps.engelsmaTuple D,
          BoundedGaps.Maynard.maxProgressionDiscrepancy
            ((c h * N - 2) + 1)
            (c h * BoundedGaps.Maynard.compatiblePairShiftModulus
              BoundedGaps.engelsmaTuple W i) := by
  classical
  unfold affineCompatiblePairShiftRaisedEndpointDiscrepancySum
  calc
    (∑ i ∈ BoundedGaps.Maynard.compatiblePairShiftIndex
        BoundedGaps.engelsmaTuple D,
      (BoundedGaps.Maynard.maxProgressionDiscrepancy
          ((c i.2 * (2 * N) - 2) + 1)
          (c i.2 * BoundedGaps.Maynard.compatiblePairShiftModulus
            BoundedGaps.engelsmaTuple W i) +
        BoundedGaps.Maynard.maxProgressionDiscrepancy
          ((c i.2 * N - 2) + 1)
          (c i.2 * BoundedGaps.Maynard.compatiblePairShiftModulus
            BoundedGaps.engelsmaTuple W i))) ≤
      ∑ i ∈ BoundedGaps.Maynard.compatiblePairShiftIndex
          BoundedGaps.engelsmaTuple D,
        ((∑ h : BoundedGaps.engelsmaTuple,
          BoundedGaps.Maynard.maxProgressionDiscrepancy
            ((c h * (2 * N) - 2) + 1)
            (c h * BoundedGaps.Maynard.compatiblePairShiftModulus
              BoundedGaps.engelsmaTuple W i)) +
        ∑ h : BoundedGaps.engelsmaTuple,
          BoundedGaps.Maynard.maxProgressionDiscrepancy
            ((c h * N - 2) + 1)
            (c h * BoundedGaps.Maynard.compatiblePairShiftModulus
              BoundedGaps.engelsmaTuple W i)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply add_le_add
      · exact Finset.single_le_sum
          (f := fun h : BoundedGaps.engelsmaTuple ↦
            BoundedGaps.Maynard.maxProgressionDiscrepancy
              ((c h * (2 * N) - 2) + 1)
              (c h * BoundedGaps.Maynard.compatiblePairShiftModulus
                BoundedGaps.engelsmaTuple W i))
          (fun h _ ↦ BoundedGaps.Maynard.maxProgressionDiscrepancy_nonneg _ _)
          (Finset.mem_univ i.2)
      · exact Finset.single_le_sum
          (f := fun h : BoundedGaps.engelsmaTuple ↦
            BoundedGaps.Maynard.maxProgressionDiscrepancy
              ((c h * N - 2) + 1)
              (c h * BoundedGaps.Maynard.compatiblePairShiftModulus
                BoundedGaps.engelsmaTuple W i))
          (fun h _ ↦ BoundedGaps.Maynard.maxProgressionDiscrepancy_nonneg _ _)
          (Finset.mem_univ i.2)
    _ = _ := by
      rw [Finset.sum_add_distrib]
      apply congrArg₂ (fun x y : ℝ ↦ x + y)
      · exact Finset.sum_comm
      · exact Finset.sum_comm

theorem eventually_const_mul_primorial_tripleLogCutoff_le_rpow
    (K : ℕ) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ M : ℕ in atTop,
      ((K * primorial (BoundedGaps.Maynard.tripleLogCutoff M) : ℕ) : ℝ) ≤
        Real.rpow (M : ℝ) eps := by
  have hepsHalf : 0 < eps / 2 := by linarith
  have hpow : Tendsto
      (fun M : ℕ ↦ Real.rpow (M : ℝ) (eps / 2)) atTop atTop :=
    (tendsto_rpow_atTop hepsHalf).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hK : ∀ᶠ M : ℕ in atTop,
      (K : ℝ) ≤ Real.rpow (M : ℝ) (eps / 2) :=
    hpow.eventually (eventually_ge_atTop (K : ℝ))
  have hW := BoundedGaps.Maynard.eventually_primorial_tripleLogCutoff_le_rpow
    hepsHalf
  filter_upwards [hK, hW, eventually_ge_atTop 1] with M hK hW hM
  have hMreal : 0 < (M : ℝ) := by exact_mod_cast hM
  calc
    ((K * primorial (BoundedGaps.Maynard.tripleLogCutoff M) : ℕ) : ℝ) =
        (K : ℝ) * (primorial (BoundedGaps.Maynard.tripleLogCutoff M) : ℝ) := by
      push_cast
      rfl
    _ ≤ Real.rpow (M : ℝ) (eps / 2) *
        Real.rpow (M : ℝ) (eps / 2) :=
      mul_le_mul hK hW (by positivity) (Real.rpow_nonneg hMreal.le _)
    _ = Real.rpow (M : ℝ) eps := by
      calc
        Real.rpow (M : ℝ) (eps / 2) * Real.rpow (M : ℝ) (eps / 2) =
            Real.rpow (M : ℝ) (eps / 2 + eps / 2) :=
          (Real.rpow_add hMreal (eps / 2) (eps / 2)).symm
        _ = Real.rpow (M : ℝ) eps := by ring_nf

theorem eventually_const_mul_engelsma_modulus_radius_cutoff
    (K : ℕ) {theta alpha eps : ℝ}
    (heps : 0 < eps) (hsum : eps + 2 * alpha ≤ theta) :
    ∀ᶠ N : ℕ in atTop,
      K * BoundedGaps.Maynard.engelsmaMaynardModulus N *
          BoundedGaps.Maynard.engelsmaMaynardRadius alpha N *
          BoundedGaps.Maynard.engelsmaMaynardRadius alpha N ≤
        BoundedGaps.Maynard.modulusCutoff theta (N - 1) := by
  have hW := eventually_const_mul_primorial_tripleLogCutoff_le_rpow K heps
  have hbase := BoundedGaps.Maynard.eventually_maynardDivisorCutoff_product_le_modulusCutoff
    (W := fun M ↦ K * primorial (BoundedGaps.Maynard.tripleLogCutoff M))
    hsum hW
  simpa [BoundedGaps.Maynard.engelsmaMaynardModulus,
    BoundedGaps.Maynard.engelsmaMaynardRadius] using
      (tendsto_sub_atTop_nat 1).eventually hbase

theorem eventually_affine_raised_endpoint_cutoffs
    {c : BoundedGaps.engelsmaTuple → ℕ} (hc : ∀ i, 0 < c i)
    {theta alpha eps : ℝ} (htheta : 0 ≤ theta)
    (heps : 0 < eps) (hsum : eps + 2 * alpha ≤ theta) :
    ∀ᶠ N : ℕ in atTop, ∀ i : BoundedGaps.engelsmaTuple,
      c i * (BoundedGaps.Maynard.engelsmaMaynardModulus N *
          BoundedGaps.Maynard.engelsmaMaynardRadius alpha N *
          BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) ≤
          BoundedGaps.Maynard.modulusCutoff theta
            ((c i * N - 2) + 1) ∧
        c i * (BoundedGaps.Maynard.engelsmaMaynardModulus N *
          BoundedGaps.Maynard.engelsmaMaynardRadius alpha N *
          BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) ≤
          BoundedGaps.Maynard.modulusCutoff theta
            ((c i * (2 * N) - 2) + 1) := by
  let K := coefficientCoverageBound c
  have hbase := eventually_const_mul_engelsma_modulus_radius_cutoff
    K heps hsum
  filter_upwards [hbase, eventually_ge_atTop 2] with N hbase hN i
  have hciK : c i ≤ K := coefficient_le_coverageBound c i
  have hlowerBase : N - 1 ≤ (c i * N - 2) + 1 := by
    have hmulN : N ≤ c i * N := Nat.le_mul_of_pos_left N (hc i)
    omega
  have hupperBase : N - 1 ≤ (c i * (2 * N) - 2) + 1 := by
    have hmulN : N ≤ c i * N := Nat.le_mul_of_pos_left N (hc i)
    have hmono : c i * N ≤ c i * (2 * N) :=
      Nat.mul_le_mul_left (c i) (by omega)
    omega
  have hmul : c i * (BoundedGaps.Maynard.engelsmaMaynardModulus N *
        BoundedGaps.Maynard.engelsmaMaynardRadius alpha N *
        BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) ≤
      K * BoundedGaps.Maynard.engelsmaMaynardModulus N *
        BoundedGaps.Maynard.engelsmaMaynardRadius alpha N *
        BoundedGaps.Maynard.engelsmaMaynardRadius alpha N := by
    calc
      c i * (BoundedGaps.Maynard.engelsmaMaynardModulus N *
          BoundedGaps.Maynard.engelsmaMaynardRadius alpha N *
          BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) ≤
        K * (BoundedGaps.Maynard.engelsmaMaynardModulus N *
          BoundedGaps.Maynard.engelsmaMaynardRadius alpha N *
          BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) :=
        Nat.mul_le_mul_right _ hciK
      _ = K * BoundedGaps.Maynard.engelsmaMaynardModulus N *
          BoundedGaps.Maynard.engelsmaMaynardRadius alpha N *
          BoundedGaps.Maynard.engelsmaMaynardRadius alpha N := by
        simp [mul_assoc]
  exact ⟨hmul.trans (hbase.trans
      (BoundedGaps.Maynard.modulusCutoff_mono htheta hlowerBase)),
    hmul.trans (hbase.trans
      (BoundedGaps.Maynard.modulusCutoff_mono htheta hupperBase))⟩

theorem primeLevelWitness_bound_abs_affineError_raised_tau
    {theta A C : ℝ} {X₀ : ℕ}
    (hw : BoundedGaps.Maynard.PrimeLevelWitness theta A C X₀)
    {c : BoundedGaps.engelsmaTuple → ℕ}
    {D : Finset (BoundedGaps.engelsmaTuple → ℕ)} {R W N : ℕ}
    {coeff : (BoundedGaps.engelsmaTuple → ℕ) → ℝ} {L : ℝ}
    (hW : Squarefree W) (hc : ∀ i, 0 < c i)
    (hcoverCoeff : CoefficientPrimesCovered c W)
    (hcoverDiff : CoefficientDifferencesCovered c W)
    (hD : ∀ d ∈ D, BoundedGaps.Maynard.IsMaynardDivisorTuple
      BoundedGaps.engelsmaTuple R W d)
    (hN : 1 < N) (hL : 0 ≤ L)
    (hbound : ∀ d ∈ D, |coeff d| ≤ L)
    (hupper : ∀ i : BoundedGaps.engelsmaTuple,
      X₀ ≤ (c i * (2 * N) - 2) + 1)
    (hlower : ∀ i : BoundedGaps.engelsmaTuple,
      X₀ ≤ (c i * N - 2) + 1)
    (hcutUpper : ∀ i : BoundedGaps.engelsmaTuple,
      c i * (W * R * R) ≤ BoundedGaps.Maynard.modulusCutoff theta
        ((c i * (2 * N) - 2) + 1))
    (hcutLower : ∀ i : BoundedGaps.engelsmaTuple,
      c i * (W * R * R) ≤ BoundedGaps.Maynard.modulusCutoff theta
        ((c i * N - 2) + 1))
    (hsizeUpper : ∀ i : BoundedGaps.engelsmaTuple,
      c i * (W * R * R) ≤ ((c i * (2 * N) - 2) + 1) + 1)
    (hsizeLower : ∀ i : BoundedGaps.engelsmaTuple,
      c i * (W * R * R) ≤ ((c i * N - 2) + 1) + 1) :
    |affineCompatiblePairRestrictedErrorOuter c D R W N coeff hD| ≤
      L ^ 2 *
        (((∑ i : BoundedGaps.engelsmaTuple,
          BoundedGaps.Maynard.tauIndexedEndpointEnvelope
            BoundedGaps.engelsmaTuple (W * R * R) C A
              ((c i * (2 * N) - 2) + 1)) +
        ∑ i : BoundedGaps.engelsmaTuple,
          BoundedGaps.Maynard.tauIndexedEndpointEnvelope
            BoundedGaps.engelsmaTuple (W * R * R) C A
              ((c i * N - 2) + 1)) +
        4 * ((BoundedGaps.Maynard.compatiblePairShiftIndex
          BoundedGaps.engelsmaTuple D).card : ℝ)) := by
  have hWpos : 0 < W := Nat.pos_of_ne_zero hW.ne_zero
  have hH : BoundedGaps.engelsmaTuple.Nonempty := by
    apply Finset.card_pos.mp
    rw [BoundedGaps.engelsmaTuple_card]
    norm_num
  have hSQ := BoundedGaps.Maynard.compatiblePairShiftModulus_image_subset_radius
    hWpos hD
  have hcoord :
      (∑ i : BoundedGaps.engelsmaTuple,
        ∑ j ∈ BoundedGaps.Maynard.compatiblePairShiftIndex
            BoundedGaps.engelsmaTuple D,
          BoundedGaps.Maynard.maxProgressionDiscrepancy
            ((c i * (2 * N) - 2) + 1)
            (c i * BoundedGaps.Maynard.compatiblePairShiftModulus
              BoundedGaps.engelsmaTuple W j)) +
      ∑ i : BoundedGaps.engelsmaTuple,
        ∑ j ∈ BoundedGaps.Maynard.compatiblePairShiftIndex
            BoundedGaps.engelsmaTuple D,
          BoundedGaps.Maynard.maxProgressionDiscrepancy
            ((c i * N - 2) + 1)
            (c i * BoundedGaps.Maynard.compatiblePairShiftModulus
              BoundedGaps.engelsmaTuple W j) ≤
      (∑ i : BoundedGaps.engelsmaTuple,
        BoundedGaps.Maynard.tauIndexedEndpointEnvelope
          BoundedGaps.engelsmaTuple (W * R * R) C A
            ((c i * (2 * N) - 2) + 1)) +
      ∑ i : BoundedGaps.engelsmaTuple,
        BoundedGaps.Maynard.tauIndexedEndpointEnvelope
          BoundedGaps.engelsmaTuple (W * R * R) C A
            ((c i * N - 2) + 1) := by
    apply add_le_add
    · apply Finset.sum_le_sum
      intro i hi
      exact primeLevelWitness_sum_scaled_maxProgressionDiscrepancy_compatiblePairShift_tau
        (x := (c i * (2 * N) - 2) + 1) (Q := W * R * R)
        hw (hupper i) hH hW hD (hc i) hSQ (hsizeUpper i) (hcutUpper i)
    · apply Finset.sum_le_sum
      intro i hi
      exact primeLevelWitness_sum_scaled_maxProgressionDiscrepancy_compatiblePairShift_tau
        (x := (c i * N - 2) + 1) (Q := W * R * R)
        hw (hlower i) hH hW hD (hc i) hSQ (hsizeLower i) (hcutLower i)
  calc
    |affineCompatiblePairRestrictedErrorOuter c D R W N coeff hD| ≤
        affineCompatiblePairRestrictedAbsoluteErrorOuter c D R W N coeff hD :=
      abs_affineCompatiblePairRestrictedErrorOuter_le_absolute hD
    _ = affineCompatiblePairShiftWeightedErrorSum c D R W N coeff hD :=
      affineCompatiblePairRestrictedAbsoluteErrorOuter_eq_weighted hD
    _ ≤ L ^ 2 * affineCompatiblePairShiftEndpointDiscrepancySum c D W N :=
      affineCompatiblePairShiftWeightedErrorSum_le hWpos hc hcoverCoeff
        hcoverDiff hD hN hL hbound
    _ ≤ L ^ 2 *
        (affineCompatiblePairShiftRaisedEndpointDiscrepancySum c D W N +
          4 * ((BoundedGaps.Maynard.compatiblePairShiftIndex
            BoundedGaps.engelsmaTuple D).card : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (affineCompatiblePairShiftEndpointDiscrepancySum_le_raised c D W N)
        (sq_nonneg L)
    _ ≤ L ^ 2 *
        (((∑ i : BoundedGaps.engelsmaTuple,
          ∑ j ∈ BoundedGaps.Maynard.compatiblePairShiftIndex
              BoundedGaps.engelsmaTuple D,
            BoundedGaps.Maynard.maxProgressionDiscrepancy
              ((c i * (2 * N) - 2) + 1)
              (c i * BoundedGaps.Maynard.compatiblePairShiftModulus
                BoundedGaps.engelsmaTuple W j)) +
        ∑ i : BoundedGaps.engelsmaTuple,
          ∑ j ∈ BoundedGaps.Maynard.compatiblePairShiftIndex
              BoundedGaps.engelsmaTuple D,
            BoundedGaps.Maynard.maxProgressionDiscrepancy
              ((c i * N - 2) + 1)
              (c i * BoundedGaps.Maynard.compatiblePairShiftModulus
                BoundedGaps.engelsmaTuple W j)) +
          4 * ((BoundedGaps.Maynard.compatiblePairShiftIndex
            BoundedGaps.engelsmaTuple D).card : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg L)
      exact add_le_add
        (affineCompatiblePairShiftRaisedEndpointDiscrepancySum_le_coordinate_sum
          c D W N) le_rfl
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg L)
      exact add_le_add hcoord le_rfl

def affineMaynardS2Error
    (c : BoundedGaps.engelsmaTuple → ℕ) (alpha : ℝ) (N : ℕ) : ℝ :=
  affineCompatiblePairRestrictedErrorOuter c
    (affineMaynardSupport alpha N)
    (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
    (BoundedGaps.Maynard.engelsmaMaynardModulus N) N
    (affineMaynardCoefficient alpha N)
    (affineMaynardS2SupportProof alpha N)

def affineMaynardS2RaisedTauErrorEnvelope
    (c : BoundedGaps.engelsmaTuple → ℕ)
    (alpha A C : ℝ) (N : ℕ) : ℝ :=
  (BoundedGaps.Maynard.engelsmaMaynardSharpCoefficientEnvelope alpha N) ^ 2 *
    (((∑ i : BoundedGaps.engelsmaTuple,
      BoundedGaps.Maynard.tauIndexedEndpointEnvelope
        BoundedGaps.engelsmaTuple
        (BoundedGaps.Maynard.engelsmaMaynardModulus N *
          BoundedGaps.Maynard.engelsmaMaynardRadius alpha N *
          BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
        C A ((c i * (2 * N) - 2) + 1)) +
    ∑ i : BoundedGaps.engelsmaTuple,
      BoundedGaps.Maynard.tauIndexedEndpointEnvelope
        BoundedGaps.engelsmaTuple
        (BoundedGaps.Maynard.engelsmaMaynardModulus N *
          BoundedGaps.Maynard.engelsmaMaynardRadius alpha N *
          BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
        C A ((c i * N - 2) + 1)) +
    4 * ((BoundedGaps.Maynard.compatiblePairShiftIndex
      BoundedGaps.engelsmaTuple (affineMaynardSupport alpha N)).card : ℝ))

def affineMaynardS2RaisedTauEndpointEnvelope
    (c : BoundedGaps.engelsmaTuple → ℕ)
    (alpha A C : ℝ) (N : ℕ) : ℝ :=
  (BoundedGaps.Maynard.engelsmaMaynardSharpCoefficientEnvelope alpha N) ^ 2 *
    ((∑ i : BoundedGaps.engelsmaTuple,
      BoundedGaps.Maynard.tauIndexedEndpointEnvelope
        BoundedGaps.engelsmaTuple
        (BoundedGaps.Maynard.engelsmaMaynardModulus N *
          BoundedGaps.Maynard.engelsmaMaynardRadius alpha N *
          BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
        C A ((c i * (2 * N) - 2) + 1)) +
    ∑ i : BoundedGaps.engelsmaTuple,
      BoundedGaps.Maynard.tauIndexedEndpointEnvelope
        BoundedGaps.engelsmaTuple
        (BoundedGaps.Maynard.engelsmaMaynardModulus N *
          BoundedGaps.Maynard.engelsmaMaynardRadius alpha N *
          BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
        C A ((c i * N - 2) + 1))

def affineMaynardS2BoundaryEnvelope
    (alpha : ℝ) (N : ℕ) : ℝ :=
  (BoundedGaps.Maynard.engelsmaMaynardSharpCoefficientEnvelope alpha N) ^ 2 *
    (4 * ((BoundedGaps.Maynard.compatiblePairShiftIndex
      BoundedGaps.engelsmaTuple (affineMaynardSupport alpha N)).card : ℝ))

theorem affineMaynardS2RaisedTauErrorEnvelope_eq
    (c : BoundedGaps.engelsmaTuple → ℕ) (alpha A C : ℝ) (N : ℕ) :
    affineMaynardS2RaisedTauErrorEnvelope c alpha A C N =
      affineMaynardS2RaisedTauEndpointEnvelope c alpha A C N +
        affineMaynardS2BoundaryEnvelope alpha N := by
  unfold affineMaynardS2RaisedTauErrorEnvelope
    affineMaynardS2RaisedTauEndpointEnvelope affineMaynardS2BoundaryEnvelope
  ring

private abbrev affineTauLogPower : ℕ :=
  (3 * Fintype.card BoundedGaps.engelsmaTuple) ^ 2

private abbrev affineCoefficientLogPower : ℕ :=
  4 * (Fintype.card BoundedGaps.engelsmaTuple) ^ 2

private abbrev affineEnvelopeLogPower : ℕ :=
  affineTauLogPower + affineCoefficientLogPower

theorem tauIndexedEndpointEnvelope_le_scaled_nat_log_ratio
    {H : Finset ℕ} {Q x N B s : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hlogN : 2 ≤ Real.log (N : ℝ))
    (hx : ((x + 1 : ℕ) : ℝ) ≤ 3 * (s : ℝ) * (N : ℝ))
    (hlogx : Real.log (N : ℝ) / 2 ≤ Real.log (x : ℝ))
    (hlogQ : 0 ≤ 1 + Real.log Q)
    (hlogQBound : 1 + Real.log Q ≤ 4 * Real.log (N : ℝ)) :
    BoundedGaps.Maynard.tauIndexedEndpointEnvelope
        H Q C ((B * 2 : ℕ) : ℝ) x ≤
      ((Fintype.card H : ℝ) * (3 * (C + 1)) * (3 * (s : ℝ)) *
          4 ^ ((3 * Fintype.card H) ^ 2) * 2 ^ B) *
        (N : ℝ) *
        (Real.log (N : ℝ)) ^ ((3 * Fintype.card H) ^ 2) /
          (Real.log (N : ℝ)) ^ B := by
  let k := Fintype.card H
  let m := (3 * k) ^ 2
  let LN := Real.log (N : ℝ)
  let LQ := 1 + Real.log Q
  let P := (k : ℝ) * (3 * (C + 1))
  have hLN : 0 < LN := by dsimp [LN]; linarith
  have hhalf : 0 < LN / 2 := by positivity
  have hlogxOne : 1 ≤ Real.log (x : ℝ) := by
    calc
      1 ≤ LN / 2 := by dsimp [LN]; linarith
      _ ≤ Real.log (x : ℝ) := hlogx
  have hpoint := BoundedGaps.Maynard.tauIndexedEndpointEnvelope_le_log_ratio
    (H := H) (Q := Q) (x := x) (B := B) hC hlogxOne hlogQ
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hpowQ : LQ ^ m ≤ (4 * LN) ^ m :=
    pow_le_pow_left₀ hlogQ hlogQBound m
  have hnum : P * ((x + 1 : ℕ) : ℝ) * LQ ^ m ≤
      P * (3 * (s : ℝ) * (N : ℝ)) * (4 * LN) ^ m := by
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hx hP) hpowQ (pow_nonneg hlogQ _)
      (mul_nonneg hP (by positivity))
  have hden : (LN / 2) ^ B ≤ (Real.log (x : ℝ)) ^ B :=
    pow_le_pow_left₀ hhalf.le hlogx B
  calc
    BoundedGaps.Maynard.tauIndexedEndpointEnvelope
        H Q C ((B * 2 : ℕ) : ℝ) x ≤
        P * ((x + 1 : ℕ) : ℝ) * LQ ^ m /
          (Real.log (x : ℝ)) ^ B := by
      simpa [P, k, m, LQ] using hpoint
    _ ≤ (P * (3 * (s : ℝ) * (N : ℝ)) * (4 * LN) ^ m) /
          (Real.log (x : ℝ)) ^ B :=
      div_le_div_of_nonneg_right hnum (pow_nonneg (by positivity) _)
    _ ≤ (P * (3 * (s : ℝ) * (N : ℝ)) * (4 * LN) ^ m) /
          (LN / 2) ^ B := by
      apply div_le_div_of_nonneg_left
      · positivity
      · exact pow_pos hhalf _
      · exact hden
    _ = ((Fintype.card H : ℝ) * (3 * (C + 1)) * (3 * (s : ℝ)) *
          4 ^ ((3 * Fintype.card H) ^ 2) * 2 ^ B) *
        (N : ℝ) *
        (Real.log (N : ℝ)) ^ ((3 * Fintype.card H) ^ 2) /
          (Real.log (N : ℝ)) ^ B := by
      dsimp [P, k, m, LN]
      rw [mul_pow, div_pow]
      field_simp

theorem abs_maynardCoefficient_le_sharp_log_bridge
    (H : Finset ℕ) (R W : ℕ) (F : (H → ℝ) → ℝ)
    (d : H → ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hF : ∀ x, |F x| ≤ B) (hH : H.Nonempty)
    (hd : d ∈ BoundedGaps.Maynard.maynardDivisorTupleSupport H R W) :
    |BoundedGaps.Maynard.maynardCoefficient H R W F d| ≤
      B * (1 + Real.log R) ^ (2 * (Fintype.card H) ^ 2) :=
  BoundedGaps.Maynard.abs_maynardCoefficient_le_sharp_log
    H R W F d B hB hF hH hd

theorem implication_elimination_bridge
    (P Q : Prop) (h : P → Q) (hp : P) : Q :=
  h hp

theorem tauIndexedEndpointEnvelope_nonneg
    {H : Finset ℕ} {Q x : ℕ} {C A : ℝ} :
    0 ≤ BoundedGaps.Maynard.tauIndexedEndpointEnvelope H Q C A x := by
  unfold BoundedGaps.Maynard.tauIndexedEndpointEnvelope
  positivity

theorem compatiblePairShiftIndex_card_le_support_sq
    (H : Finset ℕ) (D : Finset (H → ℕ)) :
    (BoundedGaps.Maynard.compatiblePairShiftIndex H D).card ≤
      D.card * D.card * H.card := by
  calc
    (BoundedGaps.Maynard.compatiblePairShiftIndex H D).card ≤
        (((D ×ˢ D).filter (fun de : (H → ℕ) × (H → ℕ) ↦
          BoundedGaps.Maynard.IsCrossCoordinateCoprime H de.1 de.2)).product
            Finset.univ).card := by
      unfold BoundedGaps.Maynard.compatiblePairShiftIndex
      exact Finset.card_filter_le _ _
    _ = ((D ×ˢ D).filter (fun de : (H → ℕ) × (H → ℕ) ↦
        BoundedGaps.Maynard.IsCrossCoordinateCoprime H de.1 de.2)).card *
          Finset.univ.card := Finset.card_product _ _
    _ ≤ (D ×ˢ D).card * Finset.univ.card := by
      exact Nat.mul_le_mul_right _ (Finset.card_filter_le _ _)
    _ = D.card * D.card * H.card := by
      rw [Finset.card_product, Finset.card_univ, Fintype.card_coe]

theorem eventually_affine_tau_endpoints_le_log_ratio
    {c : BoundedGaps.engelsmaTuple → ℕ} (hc : ∀ i, 0 < c i)
    {theta alpha eps C : ℝ}
    (halpha : 0 < alpha)
    (htheta0 : 0 < theta) (htheta1 : theta ≤ 1)
    (heps : 0 < eps) (hsum : eps + 2 * alpha ≤ theta)
    (hC : 0 ≤ C) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ᶠ N : ℕ in atTop,
      (∀ i : BoundedGaps.engelsmaTuple,
        BoundedGaps.Maynard.tauIndexedEndpointEnvelope
          BoundedGaps.engelsmaTuple
          (BoundedGaps.Maynard.engelsmaMaynardModulus N *
            BoundedGaps.Maynard.engelsmaMaynardRadius alpha N *
            BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
          C (((BoundedGaps.Maynard.engelsmaS2TauHalfLogExponent * 2 : ℕ) : ℝ))
          ((c i * (2 * N) - 2) + 1) ≤
        E * (N : ℝ) * (Real.log (N : ℝ)) ^ affineTauLogPower /
          (Real.log (N : ℝ)) ^ BoundedGaps.Maynard.engelsmaS2TauHalfLogExponent) ∧
      (∀ i : BoundedGaps.engelsmaTuple,
        BoundedGaps.Maynard.tauIndexedEndpointEnvelope
          BoundedGaps.engelsmaTuple
          (BoundedGaps.Maynard.engelsmaMaynardModulus N *
            BoundedGaps.Maynard.engelsmaMaynardRadius alpha N *
            BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
          C (((BoundedGaps.Maynard.engelsmaS2TauHalfLogExponent * 2 : ℕ) : ℝ))
          ((c i * N - 2) + 1) ≤
        E * (N : ℝ) * (Real.log (N : ℝ)) ^ affineTauLogPower /
          (Real.log (N : ℝ)) ^ BoundedGaps.Maynard.engelsmaS2TauHalfLogExponent) := by
  let K : ℕ := max 1 (coefficientCoverageBound c)
  let B : ℕ := BoundedGaps.Maynard.engelsmaS2TauHalfLogExponent
  let E : ℝ := (Fintype.card BoundedGaps.engelsmaTuple : ℝ) *
    (3 * (C + 1)) * (3 * (K : ℝ)) *
      4 ^ affineTauLogPower * 2 ^ B
  refine ⟨E, ?_, ?_⟩
  · dsimp [E]
    positivity
  have hcut := eventually_affine_raised_endpoint_cutoffs
    hc htheta0.le heps hsum
  have hlogN : ∀ᶠ N : ℕ in atTop,
      max 2 (2 * Real.log 2) ≤ Real.log (N : ℝ) := by
    have ht : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    exact ht.eventually (eventually_ge_atTop (max 2 (2 * Real.log 2)))
  have hRpos : ∀ᶠ N : ℕ in atTop,
      1 ≤ BoundedGaps.Maynard.engelsmaMaynardRadius alpha N := by
    filter_upwards [eventually_ge_atTop 3] with N hN
    unfold BoundedGaps.Maynard.engelsmaMaynardRadius
      BoundedGaps.Maynard.maynardDivisorCutoff
    apply Nat.le_floor
    have hreal := BoundedGaps.Maynard.maynardRealCutoff_gt_one
      (alpha := alpha) (N := N - 1) (show 1 < N - 1 by omega) halpha
    unfold BoundedGaps.Maynard.maynardRealCutoff at hreal
    simpa only [Nat.cast_one] using hreal.le
  filter_upwards [hcut, hlogN, hRpos,
    eventually_ge_atTop (max 3 (3 * K))] with N hcut hlogN hRpos hN
  have hKpos : 0 < K := by dsimp [K]; omega
  have hKone : 1 ≤ K := hKpos
  have hLN : 2 ≤ Real.log (N : ℝ) := (le_max_left _ _).trans hlogN
  have hLNpos : 0 < Real.log (N : ℝ) := by linarith
  have hNreal : (0 : ℝ) < N := by
    exact_mod_cast (show 0 < N by omega)
  have hQpos : 1 ≤ BoundedGaps.Maynard.engelsmaMaynardModulus N *
      BoundedGaps.Maynard.engelsmaMaynardRadius alpha N *
      BoundedGaps.Maynard.engelsmaMaynardRadius alpha N := by
    exact one_le_mul (one_le_mul (primorial_pos _) hRpos) hRpos
  have hciK (i : BoundedGaps.engelsmaTuple) : c i ≤ K :=
    (coefficient_le_coverageBound c i).trans (Nat.le_max_right _ _)
  have hendpoint (i : BoundedGaps.engelsmaTuple) (x : ℕ)
      (hxShape : x + 1 ≤ 3 * K * N)
      (hxLower : N - 1 ≤ x)
      (hQx : BoundedGaps.Maynard.engelsmaMaynardModulus N *
        BoundedGaps.Maynard.engelsmaMaynardRadius alpha N *
        BoundedGaps.Maynard.engelsmaMaynardRadius alpha N ≤ x) :
      BoundedGaps.Maynard.tauIndexedEndpointEnvelope
          BoundedGaps.engelsmaTuple
          (BoundedGaps.Maynard.engelsmaMaynardModulus N *
            BoundedGaps.Maynard.engelsmaMaynardRadius alpha N *
            BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
          C (((B * 2 : ℕ) : ℝ)) x ≤
        E * (N : ℝ) * (Real.log (N : ℝ)) ^ affineTauLogPower /
          (Real.log (N : ℝ)) ^ B := by
    let Q := BoundedGaps.Maynard.engelsmaMaynardModulus N *
      BoundedGaps.Maynard.engelsmaMaynardRadius alpha N *
      BoundedGaps.Maynard.engelsmaMaynardRadius alpha N
    have hxcast : ((x + 1 : ℕ) : ℝ) ≤ 3 * (K : ℝ) * (N : ℝ) := by
      exact_mod_cast hxShape
    have hhalfCast : (N : ℝ) / 2 ≤ (x : ℝ) := by
      have hxcast' : ((N - 1 : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast hxLower
      have hNcast : (N : ℝ) / 2 ≤ ((N - 1 : ℕ) : ℝ) := by
        have hcast : (N : ℝ) ≤ 2 * ((N - 1 : ℕ) : ℝ) := by
          exact_mod_cast (show N ≤ 2 * (N - 1) by omega)
        linarith
      exact hNcast.trans hxcast'
    have hlogHalf : Real.log (N : ℝ) / 2 ≤ Real.log ((N : ℝ) / 2) := by
      rw [Real.log_div hNreal.ne'
        (by norm_num : (2 : ℝ) ≠ 0)]
      have hlog2 := (le_max_right 2 (2 * Real.log 2)).trans hlogN
      linarith
    have hlogx : Real.log (N : ℝ) / 2 ≤ Real.log (x : ℝ) :=
      hlogHalf.trans (Real.log_le_log (by linarith) hhalfCast)
    have hlogQnonneg : 0 ≤ 1 + Real.log Q := by
      have hQreal : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQpos
      linarith [Real.log_nonneg hQreal]
    have hQleNat : Q ≤ 3 * K * N := hQx.trans (by omega)
    have hQleReal : (Q : ℝ) ≤ (3 * K : ℕ) * (N : ℝ) := by
      exact_mod_cast hQleNat
    have hconstN : (3 * K : ℕ) ≤ N := by omega
    have hconstReal : (0 : ℝ) < (3 * K : ℕ) := by positivity
    have hlogConst : Real.log ((3 * K : ℕ) : ℝ) ≤ Real.log (N : ℝ) :=
      Real.log_le_log hconstReal (by exact_mod_cast hconstN)
    have hlogQle : Real.log Q ≤ Real.log (((3 * K : ℕ) : ℝ) * (N : ℝ)) :=
      Real.log_le_log (by exact_mod_cast hQpos) hQleReal
    rw [Real.log_mul hconstReal.ne' hNreal.ne'] at hlogQle
    have hlogQBound : 1 + Real.log Q ≤ 4 * Real.log (N : ℝ) := by
      linarith
    simpa only [E] using
      (tauIndexedEndpointEnvelope_le_scaled_nat_log_ratio
        (H := BoundedGaps.engelsmaTuple) (Q := Q) (x := x) (N := N)
        (B := B) (s := K) hC hLN hxcast hlogx hlogQnonneg hlogQBound)
  constructor
  · intro i
    apply hendpoint i ((c i * (2 * N) - 2) + 1)
    · have hci := hciK i
      have hlarge : 2 ≤ c i * (2 * N) := by
        have hbase : 2 * N ≤ c i * (2 * N) :=
          Nat.le_mul_of_pos_left (2 * N) (hc i)
        omega
      calc
        (c i * (2 * N) - 2) + 1 + 1 ≤ c i * (2 * N) := by omega
        _ ≤ K * (2 * N) := Nat.mul_le_mul_right (2 * N) hci
        _ = 2 * (K * N) := by ring
        _ ≤ 3 * (K * N) := by
          have h23 : 2 ≤ 3 := by norm_num
          exact Nat.mul_le_mul_right (K * N) h23
        _ = 3 * K * N := by ring
    · have hmulN : N ≤ c i * N := Nat.le_mul_of_pos_left N (hc i)
      have hmono : c i * N ≤ c i * (2 * N) :=
        Nat.mul_le_mul_left (c i) (by omega)
      omega
    · have hxOne : 1 ≤ (c i * (2 * N) - 2) + 1 := by
        have hbase : 2 * N ≤ c i * (2 * N) :=
          Nat.le_mul_of_pos_left (2 * N) (hc i)
        omega
      exact (Nat.le_mul_of_pos_left _ (hc i)).trans
        ((hcut i).2.trans
          (BoundedGaps.Maynard.modulusCutoff_le_self hxOne htheta1))
  · intro i
    apply hendpoint i ((c i * N - 2) + 1)
    · have hci := hciK i
      have hlarge : 2 ≤ c i * N := by
        have hbase : N ≤ c i * N := Nat.le_mul_of_pos_left N (hc i)
        omega
      calc
        (c i * N - 2) + 1 + 1 ≤ c i * N := by omega
        _ ≤ K * N := Nat.mul_le_mul_right N hci
        _ ≤ 3 * (K * N) := by
          have h13 : 1 ≤ 3 := by norm_num
          simpa only [one_mul] using Nat.mul_le_mul_right (K * N) h13
        _ = 3 * K * N := by ring
    · have hmulN : N ≤ c i * N := Nat.le_mul_of_pos_left N (hc i)
      omega
    · have hxOne : 1 ≤ (c i * N - 2) + 1 := by
        have hbase : N ≤ c i * N := Nat.le_mul_of_pos_left N (hc i)
        omega
      exact (Nat.le_mul_of_pos_left _ (hc i)).trans
        ((hcut i).1.trans
          (BoundedGaps.Maynard.modulusCutoff_le_self hxOne htheta1))

set_option linter.constructorNameAsVariable false in
theorem abs_engelsmaMaynardCoefficient_le_sharp_raw
    {alpha : ℝ} (N : ℕ) {d : BoundedGaps.engelsmaTuple → ℕ}
    : d ∈ BoundedGaps.Maynard.maynardDivisorTupleSupport
        BoundedGaps.engelsmaTuple
        (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
        (BoundedGaps.Maynard.engelsmaMaynardModulus N) →
    |BoundedGaps.Maynard.maynardCoefficient
      BoundedGaps.engelsmaTuple
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
      (BoundedGaps.Maynard.engelsmaMaynardModulus N)
      BoundedGaps.Maynard.engelsmaSmallKCandidate d| ≤
    BoundedGaps.Maynard.smallKCandidateBound *
      (1 + Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)) ^
        (2 * (Fintype.card BoundedGaps.engelsmaTuple) ^ 2) := by
  have hH : BoundedGaps.engelsmaTuple.Nonempty := by
    apply Finset.card_pos.mp
    rw [BoundedGaps.engelsmaTuple_card]
    norm_num
  have hF : ∀ x : BoundedGaps.engelsmaTuple → ℝ,
      |BoundedGaps.Maynard.engelsmaSmallKCandidate x| ≤
        BoundedGaps.Maynard.smallKCandidateBound :=
    BoundedGaps.Maynard.engelsmaSmallKCandidate_abs_le
  have hs₀ := abs_maynardCoefficient_le_sharp_log_bridge
    BoundedGaps.engelsmaTuple
    (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
    (BoundedGaps.Maynard.engelsmaMaynardModulus N)
    BoundedGaps.Maynard.engelsmaSmallKCandidate d
    BoundedGaps.Maynard.smallKCandidateBound
  have hs₁ := hs₀ BoundedGaps.Maynard.smallKCandidateBound_nonneg
  have hs₂ := hs₁ hF
  have hs₃ := hs₂ hH
  exact hs₃

set_option linter.constructorNameAsVariable false in
theorem abs_affineMaynardCoefficient_le_sharp
    {alpha : ℝ} (N : ℕ) {d : BoundedGaps.engelsmaTuple → ℕ}
    : d ∈ affineMaynardSupport alpha N →
    |affineMaynardCoefficient alpha N d| ≤
      BoundedGaps.Maynard.engelsmaMaynardSharpCoefficientEnvelope alpha N := by
  unfold affineMaynardSupport affineMaynardCoefficient
    BoundedGaps.Maynard.engelsmaMaynardSharpCoefficientEnvelope
  exact abs_engelsmaMaynardCoefficient_le_sharp_raw
    (alpha := alpha) (d := d) N

set_option linter.constructorNameAsVariable false in
theorem primeLevelWitness_bound_abs_affineMaynardS2Error_raised_tau
    {theta alpha A C : ℝ} {X₀ : ℕ}
    (hw : BoundedGaps.Maynard.PrimeLevelWitness theta A C X₀)
    (htheta : theta ≤ 1)
    {c : BoundedGaps.engelsmaTuple → ℕ}
    (hc : ∀ i, 0 < c i) (N : ℕ)
    (hcoverCoeff : CoefficientPrimesCovered c
      (BoundedGaps.Maynard.engelsmaMaynardModulus N))
    (hcoverDiff : CoefficientDifferencesCovered c
      (BoundedGaps.Maynard.engelsmaMaynardModulus N))
    (hN : 1 < N)
    (hupper : ∀ i : BoundedGaps.engelsmaTuple,
      X₀ ≤ (c i * (2 * N) - 2) + 1)
    (hlower : ∀ i : BoundedGaps.engelsmaTuple,
      X₀ ≤ (c i * N - 2) + 1)
    (hcutUpper : ∀ i : BoundedGaps.engelsmaTuple,
      c i * (BoundedGaps.Maynard.engelsmaMaynardModulus N *
        BoundedGaps.Maynard.engelsmaMaynardRadius alpha N *
        BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) ≤
      BoundedGaps.Maynard.modulusCutoff theta
        ((c i * (2 * N) - 2) + 1))
    (hcutLower : ∀ i : BoundedGaps.engelsmaTuple,
      c i * (BoundedGaps.Maynard.engelsmaMaynardModulus N *
        BoundedGaps.Maynard.engelsmaMaynardRadius alpha N *
        BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) ≤
      BoundedGaps.Maynard.modulusCutoff theta
        ((c i * N - 2) + 1)) :
    |affineMaynardS2Error c alpha N| ≤
      affineMaynardS2RaisedTauErrorEnvelope c alpha A C N := by
  have hW : Squarefree (BoundedGaps.Maynard.engelsmaMaynardModulus N) := by
    unfold BoundedGaps.Maynard.engelsmaMaynardModulus
    exact BoundedGaps.Maynard.squarefree_primorial _
  have hD : ∀ d ∈ affineMaynardSupport alpha N,
      BoundedGaps.Maynard.IsMaynardDivisorTuple
      BoundedGaps.engelsmaTuple
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
      (BoundedGaps.Maynard.engelsmaMaynardModulus N) d := by
    exact affineMaynardS2SupportProof alpha N
  have hL : 0 ≤
      BoundedGaps.Maynard.engelsmaMaynardSharpCoefficientEnvelope alpha N := by
    unfold BoundedGaps.Maynard.engelsmaMaynardSharpCoefficientEnvelope
    apply mul_nonneg BoundedGaps.Maynard.smallKCandidateBound_nonneg
    positivity
  have hbound : ∀ d ∈ affineMaynardSupport alpha N,
      |affineMaynardCoefficient alpha N d| ≤
        BoundedGaps.Maynard.engelsmaMaynardSharpCoefficientEnvelope alpha N := by
    intro d
    exact abs_affineMaynardCoefficient_le_sharp
      (alpha := alpha) (d := d) N
  have hsizeUpper : ∀ i : BoundedGaps.engelsmaTuple,
      c i * (BoundedGaps.Maynard.engelsmaMaynardModulus N *
        BoundedGaps.Maynard.engelsmaMaynardRadius alpha N *
        BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) ≤
        ((c i * (2 * N) - 2) + 1) + 1 := by
    intro i
    exact (hcutUpper i).trans
      ((BoundedGaps.Maynard.modulusCutoff_le_self
        (show 1 ≤ (c i * (2 * N) - 2) + 1 by
          have hci := hc i
          omega) htheta).trans (Nat.le_succ _))
  have hsizeLower : ∀ i : BoundedGaps.engelsmaTuple,
      c i * (BoundedGaps.Maynard.engelsmaMaynardModulus N *
        BoundedGaps.Maynard.engelsmaMaynardRadius alpha N *
        BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) ≤
        ((c i * N - 2) + 1) + 1 := by
    intro i
    exact (hcutLower i).trans
      ((BoundedGaps.Maynard.modulusCutoff_le_self
        (show 1 ≤ (c i * N - 2) + 1 by
          have hci := hc i
          omega) htheta).trans (Nat.le_succ _))
  have herr := primeLevelWitness_bound_abs_affineError_raised_tau
    hw hW hc hcoverCoeff hcoverDiff hD hN hL hbound hupper hlower
      hcutUpper hcutLower hsizeUpper hsizeLower
  unfold affineMaynardS2Error affineMaynardS2RaisedTauErrorEnvelope
  exact herr

theorem exists_eventually_affineMaynardS2Error_raised_tau_envelope
    {c : BoundedGaps.engelsmaTuple → ℕ} (hc : ∀ i, 0 < c i)
    (hinj : Function.Injective c)
    {theta alpha eps A : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta ≤ 1)
    (heps : 0 < eps) (hsum : eps + 2 * alpha ≤ theta)
    (hlevel : BoundedGaps.Maynard.hasPrimeLevel theta) (hA : 0 < A) :
    ∃ C : ℝ, ∃ X₀ : ℕ,
      BoundedGaps.Maynard.PrimeLevelWitness theta A C X₀ ∧
      ∀ᶠ N : ℕ in atTop,
        |affineMaynardS2Error c alpha N| ≤
          affineMaynardS2RaisedTauErrorEnvelope c alpha A C N := by
  obtain ⟨C, X₀, hw⟩ :=
    BoundedGaps.Maynard.hasPrimeLevel_exists_witness hlevel hA
  refine ⟨C, X₀, hw, ?_⟩
  have hcut := eventually_affine_raised_endpoint_cutoffs
    hc htheta0.le heps hsum
  have hthreshold : ∀ᶠ N : ℕ in atTop,
      ∀ i : BoundedGaps.engelsmaTuple,
        X₀ ≤ (c i * N - 2) + 1 ∧
          X₀ ≤ (c i * (2 * N) - 2) + 1 := by
    filter_upwards [eventually_ge_atTop (X₀ + 2)] with N hN i
    have hmulN : N ≤ c i * N := Nat.le_mul_of_pos_left N (hc i)
    have hmono : c i * N ≤ c i * (2 * N) :=
      Nat.mul_le_mul_left (c i) (by omega)
    omega
  filter_upwards [eventually_coefficient_coverages hc hinj, hcut,
    hthreshold, eventually_ge_atTop 2] with N hcover hcut hthreshold hN
  exact primeLevelWitness_bound_abs_affineMaynardS2Error_raised_tau
    hw htheta1 hc N hcover.1 hcover.2 (by omega)
      (fun i ↦ (hthreshold i).2) (fun i ↦ (hthreshold i).1)
      (fun i ↦ (hcut i).2) (fun i ↦ (hcut i).1)

theorem exists_eventually_affineMaynardS2RaisedTauEndpointEnvelope_le_log_ratio
    {c : BoundedGaps.engelsmaTuple → ℕ} (hc : ∀ i, 0 < c i)
    {theta alpha eps C : ℝ}
    (halpha : 0 < alpha)
    (htheta0 : 0 < theta) (htheta1 : theta ≤ 1)
    (heps : 0 < eps) (hsum : eps + 2 * alpha ≤ theta)
    (hC : 0 ≤ C) :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ᶠ N : ℕ in atTop,
      affineMaynardS2RaisedTauEndpointEnvelope c alpha
          (((BoundedGaps.Maynard.engelsmaS2TauHalfLogExponent * 2 : ℕ) : ℝ)) C N ≤
        K₀ * (N : ℝ) * (Real.log (N : ℝ)) ^ affineEnvelopeLogPower /
          (Real.log (N : ℝ)) ^
            BoundedGaps.Maynard.engelsmaS2TauHalfLogExponent := by
  obtain ⟨E, hE, hendpoints⟩ := eventually_affine_tau_endpoints_le_log_ratio
    hc halpha htheta0 htheta1 heps hsum hC
  let K₀ : ℝ := BoundedGaps.Maynard.smallKCandidateBound ^ 2 *
    (1 + alpha) ^ affineCoefficientLogPower *
      ((2 * Fintype.card BoundedGaps.engelsmaTuple : ℕ) * E)
  refine ⟨K₀, ?_, ?_⟩
  · dsimp [K₀]
    positivity
  have hlogR :=
    BoundedGaps.Maynard.eventually_one_add_log_engelsmaMaynardRadius_le halpha
  have hRpos : ∀ᶠ N : ℕ in atTop,
      1 ≤ BoundedGaps.Maynard.engelsmaMaynardRadius alpha N :=
    (BoundedGaps.Maynard.eventually_one_lt_engelsmaMaynardRadius halpha).mono
      (fun _ h ↦ h.le)
  filter_upwards [hendpoints, hlogR, hRpos] with N hendpoints hlogR hRpos
  let T : ℝ := E * (N : ℝ) * (Real.log (N : ℝ)) ^ affineTauLogPower /
    (Real.log (N : ℝ)) ^ BoundedGaps.Maynard.engelsmaS2TauHalfLogExponent
  have hsumUpper :
      (∑ i : BoundedGaps.engelsmaTuple,
        BoundedGaps.Maynard.tauIndexedEndpointEnvelope
          BoundedGaps.engelsmaTuple
          (BoundedGaps.Maynard.engelsmaMaynardModulus N *
            BoundedGaps.Maynard.engelsmaMaynardRadius alpha N *
            BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
          C (((BoundedGaps.Maynard.engelsmaS2TauHalfLogExponent * 2 : ℕ) : ℝ))
          ((c i * (2 * N) - 2) + 1)) ≤
        ∑ _i : BoundedGaps.engelsmaTuple, T := by
    apply Finset.sum_le_sum
    intro i _
    exact (hendpoints.1 i : _ ≤ T)
  have hsumLower :
      (∑ i : BoundedGaps.engelsmaTuple,
        BoundedGaps.Maynard.tauIndexedEndpointEnvelope
          BoundedGaps.engelsmaTuple
          (BoundedGaps.Maynard.engelsmaMaynardModulus N *
            BoundedGaps.Maynard.engelsmaMaynardRadius alpha N *
            BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
          C (((BoundedGaps.Maynard.engelsmaS2TauHalfLogExponent * 2 : ℕ) : ℝ))
          ((c i * N - 2) + 1)) ≤
        ∑ _i : BoundedGaps.engelsmaTuple, T := by
    apply Finset.sum_le_sum
    intro i _
    exact (hendpoints.2 i : _ ≤ T)
  have hsumEndpoints :
      (∑ i : BoundedGaps.engelsmaTuple,
        BoundedGaps.Maynard.tauIndexedEndpointEnvelope
          BoundedGaps.engelsmaTuple
          (BoundedGaps.Maynard.engelsmaMaynardModulus N *
            BoundedGaps.Maynard.engelsmaMaynardRadius alpha N *
            BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
          C (((BoundedGaps.Maynard.engelsmaS2TauHalfLogExponent * 2 : ℕ) : ℝ))
          ((c i * (2 * N) - 2) + 1)) +
       ∑ i : BoundedGaps.engelsmaTuple,
        BoundedGaps.Maynard.tauIndexedEndpointEnvelope
          BoundedGaps.engelsmaTuple
          (BoundedGaps.Maynard.engelsmaMaynardModulus N *
            BoundedGaps.Maynard.engelsmaMaynardRadius alpha N *
            BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
          C (((BoundedGaps.Maynard.engelsmaS2TauHalfLogExponent * 2 : ℕ) : ℝ))
          ((c i * N - 2) + 1) ≤
        (2 * Fintype.card BoundedGaps.engelsmaTuple : ℕ) * T := by
    have hsumConst : (∑ _i : BoundedGaps.engelsmaTuple, T) =
        (Fintype.card BoundedGaps.engelsmaTuple : ℝ) * T := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        Fintype.card_coe]
    calc
      _ ≤ (∑ _i : BoundedGaps.engelsmaTuple, T) +
          ∑ _i : BoundedGaps.engelsmaTuple, T :=
        add_le_add hsumUpper hsumLower
      _ = (Fintype.card BoundedGaps.engelsmaTuple : ℝ) * T +
          (Fintype.card BoundedGaps.engelsmaTuple : ℝ) * T := by
        rw [hsumConst]
      _ = (2 * Fintype.card BoundedGaps.engelsmaTuple : ℕ) * T := by
        push_cast
        ring
  have hLRnonneg : 0 ≤ 1 + Real.log
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) := by
    have hRreal : (1 : ℝ) ≤
        BoundedGaps.Maynard.engelsmaMaynardRadius alpha N := by
      exact_mod_cast hRpos
    linarith [Real.log_nonneg hRreal]
  have hCoeffPow :
      (1 + Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)) ^
          affineCoefficientLogPower ≤
        ((1 + alpha) * Real.log (N : ℝ)) ^ affineCoefficientLogPower :=
    pow_le_pow_left₀ hLRnonneg hlogR affineCoefficientLogPower
  have hCoeff :
      (BoundedGaps.Maynard.engelsmaMaynardSharpCoefficientEnvelope alpha N) ^ 2 ≤
        BoundedGaps.Maynard.smallKCandidateBound ^ 2 *
          ((1 + alpha) * Real.log (N : ℝ)) ^ affineCoefficientLogPower := by
    unfold BoundedGaps.Maynard.engelsmaMaynardSharpCoefficientEnvelope
    have hexp :
        (2 * (Fintype.card BoundedGaps.engelsmaTuple) ^ 2) * 2 =
          affineCoefficientLogPower := by
      dsimp [affineCoefficientLogPower]
      ring
    calc
      (BoundedGaps.Maynard.smallKCandidateBound *
          (1 + Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)) ^
            (2 * (Fintype.card BoundedGaps.engelsmaTuple) ^ 2)) ^ 2 =
          BoundedGaps.Maynard.smallKCandidateBound ^ 2 *
            (1 + Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)) ^
              affineCoefficientLogPower := by
        rw [mul_pow, ← pow_mul, hexp]
      _ ≤ BoundedGaps.Maynard.smallKCandidateBound ^ 2 *
          ((1 + alpha) * Real.log (N : ℝ)) ^ affineCoefficientLogPower :=
        mul_le_mul_of_nonneg_left hCoeffPow (sq_nonneg _)
  have hEndpointNonneg : 0 ≤
      (∑ i : BoundedGaps.engelsmaTuple,
        BoundedGaps.Maynard.tauIndexedEndpointEnvelope
          BoundedGaps.engelsmaTuple
          (BoundedGaps.Maynard.engelsmaMaynardModulus N *
            BoundedGaps.Maynard.engelsmaMaynardRadius alpha N *
            BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
          C (((BoundedGaps.Maynard.engelsmaS2TauHalfLogExponent * 2 : ℕ) : ℝ))
          ((c i * (2 * N) - 2) + 1)) +
       ∑ i : BoundedGaps.engelsmaTuple,
        BoundedGaps.Maynard.tauIndexedEndpointEnvelope
          BoundedGaps.engelsmaTuple
          (BoundedGaps.Maynard.engelsmaMaynardModulus N *
            BoundedGaps.Maynard.engelsmaMaynardRadius alpha N *
            BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
          C (((BoundedGaps.Maynard.engelsmaS2TauHalfLogExponent * 2 : ℕ) : ℝ))
          ((c i * N - 2) + 1) := by
    apply add_nonneg <;> apply Finset.sum_nonneg <;> intro i _ <;>
      exact tauIndexedEndpointEnvelope_nonneg
  have hlogProductNonneg :
      0 ≤ (1 + alpha) * Real.log (N : ℝ) := hLRnonneg.trans hlogR
  have hCoeffUpperNonneg : 0 ≤
      BoundedGaps.Maynard.smallKCandidateBound ^ 2 *
        ((1 + alpha) * Real.log (N : ℝ)) ^ affineCoefficientLogPower :=
    mul_nonneg (sq_nonneg _)
      (pow_nonneg hlogProductNonneg affineCoefficientLogPower)
  have hlogPower :
      (Real.log (N : ℝ)) ^ affineCoefficientLogPower *
          (Real.log (N : ℝ)) ^ affineTauLogPower =
        (Real.log (N : ℝ)) ^ affineEnvelopeLogPower := by
    rw [pow_add]
    ring
  unfold affineMaynardS2RaisedTauEndpointEnvelope
  change (BoundedGaps.Maynard.engelsmaMaynardSharpCoefficientEnvelope alpha N) ^ 2 *
    _ ≤ _
  calc
    (BoundedGaps.Maynard.engelsmaMaynardSharpCoefficientEnvelope alpha N) ^ 2 * _ ≤
        (BoundedGaps.Maynard.smallKCandidateBound ^ 2 *
          ((1 + alpha) * Real.log (N : ℝ)) ^ affineCoefficientLogPower) *
          ((2 * Fintype.card BoundedGaps.engelsmaTuple : ℕ) * T) :=
      mul_le_mul hCoeff hsumEndpoints hEndpointNonneg hCoeffUpperNonneg
    _ = K₀ * (N : ℝ) * (Real.log (N : ℝ)) ^ affineEnvelopeLogPower /
          (Real.log (N : ℝ)) ^
            BoundedGaps.Maynard.engelsmaS2TauHalfLogExponent := by
      rw [← hlogPower]
      dsimp [K₀, T]
      rw [mul_pow]
      ring

theorem affineMaynardS2RaisedTauEndpointEnvelope_nonneg
    (c : BoundedGaps.engelsmaTuple → ℕ) (alpha A C : ℝ) (N : ℕ) :
    0 ≤ affineMaynardS2RaisedTauEndpointEnvelope c alpha A C N := by
  unfold affineMaynardS2RaisedTauEndpointEnvelope
  apply mul_nonneg (sq_nonneg _)
  apply add_nonneg <;> apply Finset.sum_nonneg <;> intro i _ <;>
    exact tauIndexedEndpointEnvelope_nonneg

theorem tendsto_affine_log_ratio_envelope_div_scale
    {alpha K₀ : ℝ} (halpha : 0 < alpha) (hK₀ : 0 ≤ K₀) :
    Tendsto
      (fun N : ℕ ↦
        (K₀ * (N : ℝ) * (Real.log (N : ℝ)) ^ affineEnvelopeLogPower /
            (Real.log (N : ℝ)) ^
              BoundedGaps.Maynard.engelsmaS2TauHalfLogExponent) /
          BoundedGaps.Maynard.engelsmaMaynardScale alpha N)
      atTop (nhds 0) := by
  have hScale :=
    BoundedGaps.Maynard.eventually_engelsmaMaynardScale_ge_nat_div_modulus_pow
      halpha
  have hScalePos := BoundedGaps.Maynard.eventually_engelsmaMaynardScale_pos halpha
  have hW := BoundedGaps.Maynard.eventually_engelsmaMaynardModulus_le_log_cube
  have hlogN : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) := by
    have ht : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    exact ht.eventually (eventually_ge_atTop 1)
  have hmajorant : Tendsto
      (fun N : ℕ ↦ K₀ / (Real.log (N : ℝ)) ^ 2) atTop (nhds 0) := by
    have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    exact (((tendsto_pow_atTop (α := ℝ) (by norm_num : (2 : ℕ) ≠ 0)).comp
      hlog).const_div_atTop K₀)
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun N ↦ abs_nonneg _) ?_ hmajorant
  filter_upwards [hScale, hScalePos, hW, hlogN,
    eventually_ge_atTop 1] with N hScale hScalePos hW hlogN hN
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hWpos : 0 < (BoundedGaps.Maynard.engelsmaMaynardModulus N : ℝ) := by
    exact_mod_cast primorial_pos (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
  have hLN : 0 < Real.log (N : ℝ) := lt_of_lt_of_le zero_lt_one hlogN
  have hWpow : (BoundedGaps.Maynard.engelsmaMaynardModulus N : ℝ) ^ 106 ≤
      (Real.log (N : ℝ)) ^ 318 := by
    calc
      (BoundedGaps.Maynard.engelsmaMaynardModulus N : ℝ) ^ 106 ≤
          ((Real.log (N : ℝ)) ^ 3) ^ 106 :=
        pow_le_pow_left₀ hWpos.le hW 106
      _ = (Real.log (N : ℝ)) ^ 318 := by rw [← pow_mul]
  have hLowerPos : 0 < (N : ℝ) /
      (BoundedGaps.Maynard.engelsmaMaynardModulus N : ℝ) ^ 106 :=
    div_pos hNreal (pow_pos hWpos _)
  have hMajorNonneg : 0 ≤
      K₀ * (N : ℝ) * (Real.log (N : ℝ)) ^ affineEnvelopeLogPower /
        (Real.log (N : ℝ)) ^
          BoundedGaps.Maynard.engelsmaS2TauHalfLogExponent := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg hK₀ hNreal.le)
        (pow_nonneg hLN.le affineEnvelopeLogPower))
      (pow_nonneg hLN.le _)
  rw [abs_of_nonneg (div_nonneg hMajorNonneg hScalePos.le)]
  calc
    (K₀ * (N : ℝ) * (Real.log (N : ℝ)) ^ affineEnvelopeLogPower /
          (Real.log (N : ℝ)) ^
            BoundedGaps.Maynard.engelsmaS2TauHalfLogExponent) /
        BoundedGaps.Maynard.engelsmaMaynardScale alpha N ≤
      (K₀ * (N : ℝ) * (Real.log (N : ℝ)) ^ affineEnvelopeLogPower /
          (Real.log (N : ℝ)) ^
            BoundedGaps.Maynard.engelsmaS2TauHalfLogExponent) /
        ((N : ℝ) /
          (BoundedGaps.Maynard.engelsmaMaynardModulus N : ℝ) ^ 106) := by
      apply div_le_div_of_nonneg_left hMajorNonneg hLowerPos hScale
    _ = K₀ * (BoundedGaps.Maynard.engelsmaMaynardModulus N : ℝ) ^ 106 *
          (Real.log (N : ℝ)) ^ affineEnvelopeLogPower /
            (Real.log (N : ℝ)) ^
              BoundedGaps.Maynard.engelsmaS2TauHalfLogExponent := by
      field_simp
    _ ≤ K₀ * (Real.log (N : ℝ)) ^ 318 *
          (Real.log (N : ℝ)) ^ affineEnvelopeLogPower /
            (Real.log (N : ℝ)) ^
              BoundedGaps.Maynard.engelsmaS2TauHalfLogExponent := by
      apply div_le_div_of_nonneg_right
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hWpow hK₀)
          (pow_nonneg hLN.le _)
      · exact pow_nonneg hLN.le _
    _ = K₀ / (Real.log (N : ℝ)) ^ 2 := by
      have hExp : BoundedGaps.Maynard.engelsmaS2TauHalfLogExponent =
          318 + affineEnvelopeLogPower + 2 := by
        unfold BoundedGaps.Maynard.engelsmaS2TauHalfLogExponent
        dsimp [affineEnvelopeLogPower, affineCoefficientLogPower,
          affineTauLogPower]
        omega
      rw [hExp, pow_add, pow_add]
      field_simp
      ring

theorem tendsto_affineMaynardS2RaisedTauEndpointEnvelope_div_scale
    {c : BoundedGaps.engelsmaTuple → ℕ} (hc : ∀ i, 0 < c i)
    {theta alpha eps C : ℝ}
    (halpha : 0 < alpha)
    (htheta0 : 0 < theta) (htheta1 : theta ≤ 1)
    (heps : 0 < eps) (hsum : eps + 2 * alpha ≤ theta)
    (hC : 0 ≤ C) :
    Tendsto
      (fun N : ℕ ↦
        affineMaynardS2RaisedTauEndpointEnvelope c alpha
            (((BoundedGaps.Maynard.engelsmaS2TauHalfLogExponent * 2 : ℕ) : ℝ)) C N /
          BoundedGaps.Maynard.engelsmaMaynardScale alpha N)
      atTop (nhds 0) := by
  obtain ⟨K₀, hK₀, hbound⟩ :=
    exists_eventually_affineMaynardS2RaisedTauEndpointEnvelope_le_log_ratio
      hc halpha htheta0 htheta1 heps hsum hC
  have hmajor := tendsto_affine_log_ratio_envelope_div_scale halpha hK₀
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun N ↦ abs_nonneg _) ?_ hmajor
  filter_upwards [hbound,
    BoundedGaps.Maynard.eventually_engelsmaMaynardScale_pos halpha] with
      N hbound hscale
  rw [abs_of_nonneg (div_nonneg
    (affineMaynardS2RaisedTauEndpointEnvelope_nonneg c alpha _ C N) hscale.le)]
  exact div_le_div_of_nonneg_right hbound hscale.le

theorem exists_eventually_affineMaynardS2BoundaryEnvelope_le_rpow_log
    {alpha : ℝ} (halpha : 0 < alpha) :
    ∃ C₀ : ℝ, ∃ m : ℕ, 0 ≤ C₀ ∧ ∀ᶠ N : ℕ in atTop,
      affineMaynardS2BoundaryEnvelope alpha N ≤
        C₀ * (Real.rpow (N : ℝ) alpha) ^ 2 *
          (Real.log (N : ℝ)) ^ m := by
  let k : ℕ := Fintype.card BoundedGaps.engelsmaTuple
  let pC : ℕ := 4 * k ^ 2
  let pD : ℕ := 2 * k
  let m : ℕ := pC + pD
  let C₀ : ℝ := 4 * (k : ℝ) * BoundedGaps.Maynard.smallKCandidateBound ^ 2 *
    (1 + alpha) ^ m
  refine ⟨C₀, m, ?_, ?_⟩
  · dsimp [C₀]
    positivity
  have hR : ∀ᶠ N : ℕ in atTop,
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N : ℝ) ≤
        Real.rpow (N : ℝ) alpha := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    unfold BoundedGaps.Maynard.engelsmaMaynardRadius
      BoundedGaps.Maynard.maynardDivisorCutoff
    have hfloor :
        ((Nat.floor (Real.rpow ((N - 1 : ℕ) : ℝ) alpha) : ℕ) : ℝ) ≤
          Real.rpow ((N - 1 : ℕ) : ℝ) alpha :=
      Nat.floor_le (Real.rpow_nonneg (by positivity) alpha)
    have hsub : ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast Nat.sub_le N 1
    exact hfloor.trans (Real.rpow_le_rpow (by positivity) hsub halpha.le)
  have hlogR :=
    BoundedGaps.Maynard.eventually_one_add_log_engelsmaMaynardRadius_le halpha
  have hRpos : ∀ᶠ N : ℕ in atTop,
      1 ≤ BoundedGaps.Maynard.engelsmaMaynardRadius alpha N :=
    (BoundedGaps.Maynard.eventually_one_lt_engelsmaMaynardRadius halpha).mono
      (fun _ h ↦ h.le)
  have hlogN : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) := by
    have ht : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    exact ht.eventually (eventually_ge_atTop 1)
  filter_upwards [hR, hlogR, hRpos, hlogN] with N hR hlogR hRpos hlogN
  let D := affineMaynardSupport alpha N
  let R : ℝ := BoundedGaps.Maynard.engelsmaMaynardRadius alpha N
  let LR : ℝ := 1 + Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
  let NR : ℝ := Real.rpow (N : ℝ) alpha
  let U : ℝ := (1 + alpha) * Real.log (N : ℝ)
  have hLRnonneg : 0 ≤ LR := by
    dsimp [LR]
    have hRreal : (1 : ℝ) ≤
        BoundedGaps.Maynard.engelsmaMaynardRadius alpha N := by
      exact_mod_cast hRpos
    linarith [Real.log_nonneg hRreal]
  have hUnonneg : 0 ≤ U := hLRnonneg.trans hlogR
  have hRnonneg : 0 ≤ R := by dsimp [R]; positivity
  have hNRnonneg : 0 ≤ NR := by dsimp [NR]; positivity
  have hDcard : (D.card : ℝ) ≤ R * LR ^ k := by
    dsimp [D, R, LR, k]
    exact BoundedGaps.Maynard.engelsmaMaynardSupport_card_le_log
      (alpha := alpha) N
  have hbaseD : R * LR ^ k ≤ NR * U ^ k :=
    mul_le_mul hR (pow_le_pow_left₀ hLRnonneg hlogR k)
      (pow_nonneg hLRnonneg k) hNRnonneg
  have hDupperNonneg : 0 ≤ NR * U ^ k :=
    mul_nonneg hNRnonneg (pow_nonneg hUnonneg k)
  have hDsq : (D.card : ℝ) ^ 2 ≤ (NR * U ^ k) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg D.card)
      (hDcard.trans hbaseD) 2
  have hcardNat := compatiblePairShiftIndex_card_le_support_sq
    BoundedGaps.engelsmaTuple D
  have hcardReal :
      ((BoundedGaps.Maynard.compatiblePairShiftIndex
        BoundedGaps.engelsmaTuple D).card : ℝ) ≤
        ((D.card * D.card * BoundedGaps.engelsmaTuple.card : ℕ) : ℝ) := by
    exact_mod_cast hcardNat
  have hexpD : k * 2 = pD := by
    dsimp [pD]
    ring
  have hcard :
      ((BoundedGaps.Maynard.compatiblePairShiftIndex
        BoundedGaps.engelsmaTuple D).card : ℝ) ≤
        NR ^ 2 * U ^ pD * (k : ℝ) := by
    calc
      _ ≤ ((D.card * D.card * BoundedGaps.engelsmaTuple.card : ℕ) : ℝ) :=
        hcardReal
      _ = (D.card : ℝ) ^ 2 * (k : ℝ) := by
        dsimp [k]
        push_cast
        rw [Fintype.card_coe]
        ring
      _ ≤ (NR * U ^ k) ^ 2 * (k : ℝ) :=
        mul_le_mul_of_nonneg_right hDsq (Nat.cast_nonneg k)
      _ = NR ^ 2 * U ^ pD * (k : ℝ) := by
        rw [mul_pow, ← pow_mul, hexpD]
  have hexpC : (2 * k ^ 2) * 2 = pC := by
    dsimp [pC]
    ring
  have hCoeff :
      (BoundedGaps.Maynard.engelsmaMaynardSharpCoefficientEnvelope alpha N) ^ 2 ≤
        BoundedGaps.Maynard.smallKCandidateBound ^ 2 * U ^ pC := by
    unfold BoundedGaps.Maynard.engelsmaMaynardSharpCoefficientEnvelope
    calc
      (BoundedGaps.Maynard.smallKCandidateBound * LR ^ (2 * k ^ 2)) ^ 2 =
          BoundedGaps.Maynard.smallKCandidateBound ^ 2 * LR ^ pC := by
        rw [mul_pow, ← pow_mul, hexpC]
      _ ≤ BoundedGaps.Maynard.smallKCandidateBound ^ 2 * U ^ pC :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hLRnonneg hlogR pC) (sq_nonneg _)
  have hcardFour :
      4 * ((BoundedGaps.Maynard.compatiblePairShiftIndex
        BoundedGaps.engelsmaTuple D).card : ℝ) ≤
        4 * (NR ^ 2 * U ^ pD * (k : ℝ)) :=
    mul_le_mul_of_nonneg_left hcard (by norm_num)
  have hCoeffUpperNonneg : 0 ≤
      BoundedGaps.Maynard.smallKCandidateBound ^ 2 * U ^ pC :=
    mul_nonneg (sq_nonneg _) (pow_nonneg hUnonneg pC)
  have hCardFactorNonneg : 0 ≤
      4 * ((BoundedGaps.Maynard.compatiblePairShiftIndex
        BoundedGaps.engelsmaTuple D).card : ℝ) :=
    mul_nonneg (by norm_num) (Nat.cast_nonneg _)
  have hpowCombine : U ^ pC * U ^ pD = U ^ m := by
    dsimp [m]
    rw [pow_add]
  have hUfactor : U ^ m = (1 + alpha) ^ m *
      (Real.log (N : ℝ)) ^ m := by
    dsimp [U]
    rw [mul_pow]
  unfold affineMaynardS2BoundaryEnvelope
  change (BoundedGaps.Maynard.engelsmaMaynardSharpCoefficientEnvelope alpha N) ^ 2 *
    (4 * ((BoundedGaps.Maynard.compatiblePairShiftIndex
      BoundedGaps.engelsmaTuple D).card : ℝ)) ≤ _
  calc
    _ ≤ (BoundedGaps.Maynard.smallKCandidateBound ^ 2 * U ^ pC) *
        (4 * (NR ^ 2 * U ^ pD * (k : ℝ))) :=
      mul_le_mul hCoeff hcardFour hCardFactorNonneg hCoeffUpperNonneg
    _ = 4 * (k : ℝ) * BoundedGaps.Maynard.smallKCandidateBound ^ 2 *
        NR ^ 2 * (U ^ pC * U ^ pD) := by ring
    _ = 4 * (k : ℝ) * BoundedGaps.Maynard.smallKCandidateBound ^ 2 *
        NR ^ 2 * U ^ m := by rw [hpowCombine]
    _ = C₀ * (Real.rpow (N : ℝ) alpha) ^ 2 *
        (Real.log (N : ℝ)) ^ m := by
      rw [hUfactor]
      dsimp [C₀, NR]
      ring

theorem affineMaynardS2BoundaryEnvelope_nonneg (alpha : ℝ) (N : ℕ) :
    0 ≤ affineMaynardS2BoundaryEnvelope alpha N := by
  unfold affineMaynardS2BoundaryEnvelope
  apply mul_nonneg (sq_nonneg _)
  exact mul_nonneg (by norm_num) (Nat.cast_nonneg _)

theorem tendsto_affineMaynardS2BoundaryEnvelope_div_scale
    {alpha : ℝ} (halpha : 0 < alpha) (halphaQuarter : alpha < 1 / 4) :
    Tendsto
      (fun N : ℕ ↦ affineMaynardS2BoundaryEnvelope alpha N /
        BoundedGaps.Maynard.engelsmaMaynardScale alpha N)
      atTop (nhds 0) := by
  obtain ⟨C₀, m, hC₀, hEnvelope⟩ :=
    exists_eventually_affineMaynardS2BoundaryEnvelope_le_rpow_log halpha
  let eps : ℝ := (1 - 2 * alpha) / 212
  have heps : 0 < eps := by
    dsimp [eps]
    linarith
  have hexp : 2 * alpha + 106 * eps < 1 := by
    dsimp [eps]
    linarith
  have hscale := BoundedGaps.Maynard.engelsmaMaynardScale_ge_rpow halpha heps
  have hscalePos := BoundedGaps.Maynard.eventually_engelsmaMaynardScale_pos halpha
  have hlogN : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) := by
    have ht : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    exact ht.eventually (eventually_ge_atTop 1)
  have hgeneric : Tendsto
      (fun N : ℕ ↦ C₀ * Real.rpow (N : ℝ) (2 * alpha + 106 * eps) *
        Real.rpow (Real.log (N : ℝ)) (m : ℝ) / (N : ℝ))
      atTop (nhds 0) := by
    simpa [mul_assoc, mul_div_assoc] using
      (BoundedGaps.Maynard.tendsto_natCast_rpow_mul_log_rpow_div
        (a := 2 * alpha + 106 * eps) (b := (m : ℝ)) hexp).const_mul C₀
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun N ↦ abs_nonneg _) ?_ hgeneric
  filter_upwards [hEnvelope, hscale, hscalePos, hlogN,
    eventually_ge_atTop 1] with N hEnvelope hscale hscalePos hlogN hN
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hLowerPos : 0 < Real.rpow (N : ℝ) (1 - 106 * eps) :=
    Real.rpow_pos_of_pos hNpos _
  have hBoundNonneg : 0 ≤
      C₀ * (Real.rpow (N : ℝ) alpha) ^ 2 *
        (Real.log (N : ℝ)) ^ m :=
    mul_nonneg
      (mul_nonneg hC₀ (sq_nonneg _))
      (pow_nonneg (zero_le_one.trans hlogN) m)
  have hpow2 : (Real.rpow (N : ℝ) alpha) ^ 2 =
      Real.rpow (N : ℝ) (2 * alpha) := by
    calc
      (Real.rpow (N : ℝ) alpha) ^ 2 =
          (Real.rpow (N : ℝ) alpha) ^ (2 : ℝ) := by
            exact (Real.rpow_natCast (Real.rpow (N : ℝ) alpha) 2).symm
      _ = Real.rpow (N : ℝ) (alpha * (2 : ℝ)) :=
        (Real.rpow_mul hNpos.le alpha (2 : ℝ)).symm
      _ = Real.rpow (N : ℝ) (2 * alpha) := by
        congr 1
        ring
  have hlogpow : (Real.log (N : ℝ)) ^ m =
      Real.rpow (Real.log (N : ℝ)) (m : ℝ) :=
    (Real.rpow_natCast (Real.log (N : ℝ)) m).symm
  rw [abs_of_nonneg (div_nonneg
    (affineMaynardS2BoundaryEnvelope_nonneg alpha N) hscalePos.le)]
  calc
    affineMaynardS2BoundaryEnvelope alpha N /
        BoundedGaps.Maynard.engelsmaMaynardScale alpha N ≤
      (C₀ * (Real.rpow (N : ℝ) alpha) ^ 2 *
        (Real.log (N : ℝ)) ^ m) /
          BoundedGaps.Maynard.engelsmaMaynardScale alpha N :=
      div_le_div_of_nonneg_right hEnvelope hscalePos.le
    _ ≤ (C₀ * (Real.rpow (N : ℝ) alpha) ^ 2 *
        (Real.log (N : ℝ)) ^ m) /
          Real.rpow (N : ℝ) (1 - 106 * eps) := by
      apply div_le_div_of_nonneg_left hBoundNonneg hLowerPos hscale
    _ = C₀ * Real.rpow (N : ℝ) (2 * alpha + 106 * eps) *
        Real.rpow (Real.log (N : ℝ)) (m : ℝ) / (N : ℝ) := by
      rw [hpow2, hlogpow]
      have hlowinv :
          (Real.rpow (N : ℝ) (1 - 106 * eps))⁻¹ =
            Real.rpow (N : ℝ) (-(1 - 106 * eps)) :=
        (Real.rpow_neg hNpos.le _).symm
      have hninv : (N : ℝ)⁻¹ = Real.rpow (N : ℝ) (-1) := by
        calc
          (N : ℝ)⁻¹ = (Real.rpow (N : ℝ) 1)⁻¹ := by
            congr 1
            exact (Real.rpow_one (N : ℝ)).symm
          _ = Real.rpow (N : ℝ) (-1) :=
            (Real.rpow_neg hNpos.le 1).symm
      simp only [div_eq_mul_inv, hlowinv, hninv]
      calc
        C₀ * Real.rpow (N : ℝ) (2 * alpha) *
              Real.rpow (Real.log (N : ℝ)) (m : ℝ) *
              Real.rpow (N : ℝ) (-(1 - 106 * eps)) =
            C₀ * Real.rpow (Real.log (N : ℝ)) (m : ℝ) *
              (Real.rpow (N : ℝ) (2 * alpha) *
                Real.rpow (N : ℝ) (-(1 - 106 * eps))) := by ring
        _ = C₀ * Real.rpow (Real.log (N : ℝ)) (m : ℝ) *
              Real.rpow (N : ℝ) (2 * alpha + (-(1 - 106 * eps))) := by
          exact congrArg
            (fun t : ℝ ↦ C₀ * Real.rpow (Real.log (N : ℝ)) (m : ℝ) * t)
            (Real.rpow_add hNpos (2 * alpha) (-(1 - 106 * eps))).symm
        _ = C₀ * Real.rpow (Real.log (N : ℝ)) (m : ℝ) *
              Real.rpow (N : ℝ) (2 * alpha + 106 * eps) *
              Real.rpow (N : ℝ) (-1) := by
          have hExp : 2 * alpha + (-(1 - 106 * eps)) =
              (2 * alpha + 106 * eps) + (-1) := by ring
          rw [hExp]
          simpa [mul_assoc] using congrArg
            (fun t : ℝ ↦ C₀ * Real.rpow (Real.log (N : ℝ)) (m : ℝ) * t)
            (Real.rpow_add hNpos (2 * alpha + 106 * eps) (-1))
        _ = C₀ * Real.rpow (N : ℝ) (2 * alpha + 106 * eps) *
              Real.rpow (Real.log (N : ℝ)) (m : ℝ) *
              Real.rpow (N : ℝ) (-1) := by ring

theorem tendsto_affineMaynardS2RaisedTauErrorEnvelope_div_scale
    {c : BoundedGaps.engelsmaTuple → ℕ} (hc : ∀ i, 0 < c i)
    {theta alpha eps C : ℝ}
    (halpha : 0 < alpha) (halphaQuarter : alpha < 1 / 4)
    (htheta0 : 0 < theta) (htheta1 : theta ≤ 1)
    (heps : 0 < eps) (hsum : eps + 2 * alpha ≤ theta)
    (hC : 0 ≤ C) :
    Tendsto
      (fun N : ℕ ↦
        affineMaynardS2RaisedTauErrorEnvelope c alpha
            (((BoundedGaps.Maynard.engelsmaS2TauHalfLogExponent * 2 : ℕ) : ℝ)) C N /
          BoundedGaps.Maynard.engelsmaMaynardScale alpha N)
      atTop (nhds 0) := by
  have hendpoint :=
    tendsto_affineMaynardS2RaisedTauEndpointEnvelope_div_scale
      hc halpha htheta0 htheta1 heps hsum hC
  have hboundary :=
    tendsto_affineMaynardS2BoundaryEnvelope_div_scale halpha halphaQuarter
  have hadd := hendpoint.add hboundary
  simpa only [affineMaynardS2RaisedTauErrorEnvelope_eq, add_div, add_zero]
    using hadd

theorem tendsto_affineMaynardS2Error_div_scale_of_primeLevel
    {c : BoundedGaps.engelsmaTuple → ℕ} (hc : ∀ i, 0 < c i)
    (hinj : Function.Injective c)
    {theta alpha eps : ℝ}
    (halpha : 0 < alpha) (halphaQuarter : alpha < 1 / 4)
    (htheta0 : 0 < theta) (htheta1 : theta ≤ 1)
    (heps : 0 < eps) (hsum : eps + 2 * alpha ≤ theta)
    (hlevel : BoundedGaps.Maynard.hasPrimeLevel theta) :
    Tendsto
      (fun N : ℕ ↦ affineMaynardS2Error c alpha N /
        BoundedGaps.Maynard.engelsmaMaynardScale alpha N)
      atTop (nhds 0) := by
  let A : ℝ :=
    ((BoundedGaps.Maynard.engelsmaS2TauHalfLogExponent * 2 : ℕ) : ℝ)
  have hA : 0 < A := by
    dsimp [A, BoundedGaps.Maynard.engelsmaS2TauHalfLogExponent]
    positivity
  obtain ⟨C, X₀, hw, hbound⟩ :=
    exists_eventually_affineMaynardS2Error_raised_tau_envelope
      hc hinj htheta0 htheta1 heps hsum hlevel hA
  have henv := tendsto_affineMaynardS2RaisedTauErrorEnvelope_div_scale
    hc halpha halphaQuarter htheta0 htheta1 heps hsum hw.1
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun N ↦ abs_nonneg _) ?_ henv
  filter_upwards [hbound,
    BoundedGaps.Maynard.eventually_engelsmaMaynardScale_pos halpha] with
      N hbound hscale
  rw [abs_div, abs_of_pos hscale]
  exact div_le_div_of_nonneg_right hbound hscale.le

theorem eventually_engelsmaMaynardRadius_add_one_le
    {alpha : ℝ} (halphaOne : alpha ≤ 1) :
    ∀ᶠ N : ℕ in atTop,
      BoundedGaps.Maynard.engelsmaMaynardRadius alpha N + 1 ≤ N := by
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hbase : (1 : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ N - 1 by omega)
  have hpow : Real.rpow ((N - 1 : ℕ) : ℝ) alpha ≤
      Real.rpow ((N - 1 : ℕ) : ℝ) 1 :=
    Real.rpow_le_rpow_of_exponent_le hbase halphaOne
  have hfloor : BoundedGaps.Maynard.engelsmaMaynardRadius alpha N ≤ N - 1 := by
    unfold BoundedGaps.Maynard.engelsmaMaynardRadius
      BoundedGaps.Maynard.maynardDivisorCutoff
    apply Nat.floor_le_of_le
    calc
      Real.rpow ((N - 1 : ℕ) : ℝ) alpha ≤
          Real.rpow ((N - 1 : ℕ) : ℝ) 1 := hpow
      _ = ((N - 1 : ℕ) : ℝ) := by simp
  omega

theorem eventually_affineMaynardS2_eq_main_add_error
    {c : BoundedGaps.engelsmaTuple → ℕ} (hc : ∀ i, 0 < c i)
    (hinj : Function.Injective c)
    {alpha : ℝ} (halphaOne : alpha ≤ 1) :
    ∀ᶠ N : ℕ in atTop,
      primeWeightedSum c N (affineMaynardWeight c alpha N) =
        affineMaynardS2Main c alpha N + affineMaynardS2Error c alpha N := by
  filter_upwards [eventually_coefficient_coverages hc hinj,
    eventually_engelsmaMaynardRadius_add_one_le halphaOne] with
      N hcover hRN
  have hD := affineMaynardS2SupportProof alpha N
  unfold affineMaynardWeight
  rw [primeWeightedSum_preSieved_eq_compatible hD hcover.2]
  rw [affineCompatiblePrimeWeightedPairSum_eq_main_add_error
    hc hcover.1 hD hRN]
  rw [affineConcreteRestrictedMainOuter_eq_affineMaynardS2Main hc hcover.1]
  unfold affineMaynardS2Error
  congr

theorem tendsto_affineMaynardS2_div_scale_of_primeLevel
    {c : BoundedGaps.engelsmaTuple → ℕ} (hc : ∀ i, 0 < c i)
    (hinj : Function.Injective c)
    {theta alpha eps : ℝ}
    (halpha : 0 < alpha) (halphaQuarter : alpha < 1 / 4)
    (htheta0 : 0 < theta) (htheta1 : theta ≤ 1)
    (heps : 0 < eps) (hsum : eps + 2 * alpha ≤ theta)
    (hlevel : BoundedGaps.Maynard.hasPrimeLevel theta)
    (hpnt : Tendsto
      (fun n : ℕ ↦
        (BoundedGaps.Maynard.primeCountTotal n : ℝ) *
          Real.log (n : ℝ) / (n : ℝ)) atTop (nhds 1)) :
    Tendsto
      (fun N : ℕ ↦
        primeWeightedSum c N (affineMaynardWeight c alpha N) /
          BoundedGaps.Maynard.engelsmaMaynardScale alpha N)
      atTop (nhds (alpha *
        (∑ i : Fin 105, BoundedGaps.Maynard.maynardJ 105 i
          BoundedGaps.Maynard.smallKCandidate))) := by
  have hmain := tendsto_affineMaynardS2Main_div_scale_of_pnt hc halpha hpnt
  have herr := tendsto_affineMaynardS2Error_div_scale_of_primeLevel
    hc hinj halpha halphaQuarter htheta0 htheta1 heps hsum hlevel
  have hadd := hmain.add herr
  have hsumLimit : Tendsto
      (fun N : ℕ ↦
        (affineMaynardS2Main c alpha N + affineMaynardS2Error c alpha N) /
          BoundedGaps.Maynard.engelsmaMaynardScale alpha N)
      atTop (nhds (alpha *
        (∑ i : Fin 105, BoundedGaps.Maynard.maynardJ 105 i
          BoundedGaps.Maynard.smallKCandidate))) := by
    simpa only [add_div, add_zero] using hadd
  apply hsumLimit.congr'
  filter_upwards [eventually_affineMaynardS2_eq_main_add_error
    hc hinj (by linarith : alpha ≤ 1)] with N hN
  rw [hN]

/-! ## Unconditional positivity and the affine-prime theorem -/

/-- The unconditional distribution theorems and the checked 105-variable
Maynard test function produce a concrete radius exponent for which the affine
sieve excess is eventually positive. -/
theorem exists_eventually_affineMaynardExcess_pos
    {c : BoundedGaps.engelsmaTuple → ℕ} (hc : ∀ i, 0 < c i)
    (hinj : Function.Injective c) :
    ∃ alpha : ℝ, ∀ᶠ N : ℕ in atTop,
      0 < excess c N (affineMaynardWeight c alpha N) := by
  obtain ⟨theta, delta, htheta0, hthetaHalf, hlevel, hdelta0,
      hdeltaHalf, hmainPos⟩ :=
    BoundedGaps.Maynard.exists_smallKCandidate_level_delta_with_positive_mainTerm
      BoundedGaps.Maynard.unconditional_bombieriVinogradov
  have halpha : 0 < theta / 2 - delta := by linarith
  have halphaQuarter : theta / 2 - delta < 1 / 4 := by linarith
  have htheta1 : theta ≤ 1 := by linarith
  have hsum : delta + 2 * (theta / 2 - delta) ≤ theta := by linarith
  have hpnt : Tendsto
      (fun n : ℕ ↦
        (BoundedGaps.Maynard.primeCountTotal n : ℝ) *
          Real.log (n : ℝ) / (n : ℝ)) atTop (nhds 1) := by
    simpa only [BoundedGaps.Maynard.primeCountTotal,
      BoundedGaps.ordinaryPrimeNumberTheorem] using
        BoundedGaps.unconditional_ordinaryPrimeNumberTheorem
  have hS2 := tendsto_affineMaynardS2_div_scale_of_primeLevel
    hc hinj halpha halphaQuarter htheta0 htheta1 hdelta0 hsum hlevel hpnt
  have hS1 := tendsto_affineMaynardS1_div_scale
    hc hinj halpha halphaQuarter
  have hnormalized : Tendsto
      (fun N : ℕ ↦
        excess c N (affineMaynardWeight c (theta / 2 - delta) N) /
          BoundedGaps.Maynard.engelsmaMaynardScale (theta / 2 - delta) N)
      atTop (nhds ((theta / 2 - delta) *
        (∑ i : Fin 105, BoundedGaps.Maynard.maynardJ 105 i
          BoundedGaps.Maynard.smallKCandidate) -
        BoundedGaps.Maynard.maynardI 105
          BoundedGaps.Maynard.smallKCandidate)) := by
    apply (hS2.sub hS1).congr'
    filter_upwards [] with N
    unfold excess
    ring
  refine ⟨theta / 2 - delta, ?_⟩
  have hnormalizedPos := hnormalized.eventually (eventually_gt_nhds hmainPos)
  filter_upwards [hnormalizedPos,
    BoundedGaps.Maynard.eventually_engelsmaMaynardScale_pos halpha] with
      N hquotient hscale
  calc
    0 < (excess c N (affineMaynardWeight c (theta / 2 - delta) N) /
        BoundedGaps.Maynard.engelsmaMaynardScale (theta / 2 - delta) N) *
      BoundedGaps.Maynard.engelsmaMaynardScale (theta / 2 - delta) N :=
        mul_pos hquotient hscale
    _ = excess c N (affineMaynardWeight c (theta / 2 - delta) N) := by
      exact div_mul_cancel₀ _ hscale.ne'

/-- The exact unequal-slope affine-prime conclusion on the concrete
105-element coordinate type. -/
theorem affinePrimePair_engelsma
    {c : BoundedGaps.engelsmaTuple → ℕ} (hc : ∀ i, 0 < c i)
    (hinj : Function.Injective c) :
    ∀ B : ℕ, ∃ n : ℕ, ∃ i j : BoundedGaps.engelsmaTuple,
      B < n ∧ i ≠ j ∧
      (c i * n - 1).Prime ∧ (c j * n - 1).Prime := by
  apply affinePrimePair_of_eventually_positive
  obtain ⟨alpha, hpositive⟩ :=
    exists_eventually_affineMaynardExcess_pos hc hinj
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hpositive
  refine ⟨N₀, fun N hN ↦ ⟨affineMaynardWeight c alpha N, ?_, hN₀ N hN⟩⟩
  intro n hn
  unfold affineMaynardWeight
  exact preSievedWeight_nonneg _ _ _ _ _

/-- The unconditional 105-form theorem in the `Fin 105` interface used by
the elementary Pollack construction. -/
theorem affinePrimePairProperty_105 : AffinePrimePairProperty 105 := by
  intro c hc hinj B
  let e : BoundedGaps.engelsmaTuple ≃ Fin 105 :=
    Fintype.equivOfCardEq (by
      rw [Fintype.card_coe, BoundedGaps.engelsmaTuple_card,
        Fintype.card_fin])
  let c' : BoundedGaps.engelsmaTuple → ℕ := fun i ↦ c (e i)
  have hc' : ∀ i, 0 < c' i := fun i ↦ hc (e i)
  have hinj' : Function.Injective c' := hinj.comp e.injective
  obtain ⟨x, i, j, hBx, hij, hpi, hpj⟩ :=
    affinePrimePair_engelsma hc' hinj' B
  have heij : e i ≠ e j := fun he ↦ hij (e.injective he)
  rcases lt_or_gt_of_ne heij with heij_lt | hji_lt
  · exact ⟨x, e i, e j, hBx, heij_lt, by simpa [c'] using hpi,
      by simpa [c'] using hpj⟩
  · exact ⟨x, e j, e i, hBx, hji_lt, by simpa [c'] using hpj,
      by simpa [c'] using hpi⟩

end AffineSieve

end

end Erdos823
