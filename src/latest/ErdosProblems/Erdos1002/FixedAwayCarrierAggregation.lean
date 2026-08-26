import ErdosProblems.Erdos1002.FixedAwayUniformConstants
import ErdosProblems.Erdos1002.NearResonantCarrierSeries

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Uniform aggregation of the fixed-away shifted carriers

The one-carrier estimates are useful only if summing the Bernoulli Fourier
modes does not introduce a cardinality loss.  This file keeps the exact
carrier coefficient, converts the real square sum into `coefficientEnergy`,
and applies weighted Cauchy--Schwarz.  The resulting bound is uniform in the
symmetric carrier cutoff.
-/

open Filter MeasureTheory Set
open scoped BigOperators ComplexConjugate Real Topology ENNReal

namespace Erdos1002

noncomputable section

/-! ## Exact dyadic denominator partitions -/

/-- Literal coefficient sum over one half-open denominator interval. -/
def fixedAwayShiftedDenominatorRangeCoefficients
    (t δ : ℝ) (N : ℕ) (ell : ℤ) (Q U : ℕ) (n : ℤ) : ℂ :=
  fixedAwayRamanujanProfileBlock (Finset.Ioc Q U)
    (fixedAwayShiftedProfile t δ N ell) n

/-- The low exponent set is exactly the denominator interval
`(2,2^(M+1)]`; no dyadic endpoint is dropped or counted twice. -/
theorem fixedAwayShiftedDyadicTotalSum_eq_denominatorRange
    (t δ : ℝ) (N M : ℕ) (ell : ℤ) :
    fixedAwayShiftedDyadicTotalSum t δ N M ell =
      fixedAwayShiftedDenominatorRangeCoefficients
        t δ N ell 2 (2 ^ (M + 1)) := by
  induction M with
  | zero =>
      funext n
      simp [fixedAwayShiftedDyadicTotalSum, nearCarrierDyadicExponents,
        fixedAwayShiftedDenominatorRangeCoefficients,
        fixedAwayRamanujanProfileBlock]
  | succ M ih =>
      have hexponents : nearCarrierDyadicExponents (M + 1) =
          insert (M + 2) (nearCarrierDyadicExponents M) := by
        ext s
        simp only [nearCarrierDyadicExponents, Finset.mem_Ico,
          Finset.mem_insert]
        omega
      have hnew : M + 2 ∉ nearCarrierDyadicExponents M := by
        simp [nearCarrierDyadicExponents]
      have hpowDiv : 2 ^ (M + 2) / 2 = 2 ^ (M + 1) := by
        rw [pow_succ]
        omega
      funext n
      unfold fixedAwayShiftedDyadicTotalSum
      rw [hexponents, Finset.sum_insert hnew]
      change fixedAwayShiftedExponentBlock t δ N ell (M + 2) n +
          fixedAwayShiftedDyadicTotalSum t δ N M ell n = _
      rw [congrFun ih n]
      unfold fixedAwayShiftedExponentBlock fixedAwayShiftedDyadicBlock
        fixedAwayDyadicDenominators
        fixedAwayShiftedDenominatorRangeCoefficients
      rw [hpowDiv]
      have htop : 2 * 2 ^ (M + 1) = 2 ^ (M + 2) := by
        simp only [pow_succ]
        ring
      rw [htop, show M + 1 + 1 = M + 2 by omega]
      have hlower : 2 ≤ 2 ^ (M + 1) := by
        simpa only [pow_one] using!
          (Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : 1 ≤ M + 1))
      have horder : 2 ^ (M + 1) ≤ 2 ^ (M + 2) :=
        Nat.pow_le_pow_right (by omega : 0 < 2) (by omega)
      have hdisjoint : Disjoint
          (Finset.Ioc 2 (2 ^ (M + 1)))
          (Finset.Ioc (2 ^ (M + 1)) (2 ^ (M + 2))) :=
        Finset.Ioc_disjoint_Ioc_of_le le_rfl
      unfold fixedAwayRamanujanProfileBlock
      rw [add_comm, ← Finset.sum_union hdisjoint,
        Finset.Ioc_union_Ioc_eq_Ioc hlower horder]

/-- Consecutive high exponents are exactly one half-open denominator
interval, again with literal endpoint conventions. -/
theorem fixedAwayShiftedExponentRangeSum_eq_denominatorRange
    (t δ : ℝ) (N S H : ℕ) (ell : ℤ) (hS : 1 ≤ S) :
    fixedAwayShiftedExponentFinsetSum
        (nearCarrierDyadicRangeExponents S H) t δ N ell =
      fixedAwayShiftedDenominatorRangeCoefficients t δ N ell
        ((2 ^ S) / 2) ((2 ^ (S + H)) / 2) := by
  induction H with
  | zero =>
      funext n
      simp [fixedAwayShiftedExponentFinsetSum,
        nearCarrierDyadicRangeExponents,
        fixedAwayShiftedDenominatorRangeCoefficients,
        fixedAwayRamanujanProfileBlock]
  | succ H ih =>
      have hexponents : nearCarrierDyadicRangeExponents S (H + 1) =
          insert (S + H) (nearCarrierDyadicRangeExponents S H) := by
        ext s
        simp only [nearCarrierDyadicRangeExponents, Finset.mem_Ico,
          Finset.mem_insert]
        omega
      have hnew : S + H ∉ nearCarrierDyadicRangeExponents S H := by
        simp [nearCarrierDyadicRangeExponents]
      have hnext : 2 ^ (S + (H + 1)) / 2 = 2 ^ (S + H) := by
        rw [show S + (H + 1) = S + H + 1 by omega, pow_succ]
        omega
      funext n
      unfold fixedAwayShiftedExponentFinsetSum
      rw [hexponents, Finset.sum_insert hnew]
      change fixedAwayShiftedExponentBlock t δ N ell (S + H) n +
          fixedAwayShiftedExponentFinsetSum
            (nearCarrierDyadicRangeExponents S H) t δ N ell n = _
      rw [congrFun ih n]
      unfold fixedAwayShiftedExponentBlock fixedAwayShiftedDyadicBlock
        fixedAwayDyadicDenominators
        fixedAwayShiftedDenominatorRangeCoefficients
      rw [hnext, add_comm]
      rw [two_mul_pow_two_div_two (by omega : 1 ≤ S + H)]
      have horder : (2 ^ S) / 2 ≤ (2 ^ (S + H)) / 2 :=
        Nat.div_le_div_right
          (Nat.pow_le_pow_right (by omega : 0 < 2) (by omega))
      have hdisjoint : Disjoint
          (Finset.Ioc ((2 ^ S) / 2) ((2 ^ (S + H)) / 2))
          (Finset.Ioc ((2 ^ (S + H)) / 2) (2 ^ (S + H))) :=
        Finset.Ioc_disjoint_Ioc_of_le le_rfl
      unfold fixedAwayRamanujanProfileBlock
      rw [← Finset.sum_union hdisjoint,
        Finset.Ioc_union_Ioc_eq_Ioc horder]
      exact Nat.div_le_self _ _

/-! ## Real square sums and `coefficientEnergy` -/

theorem coefficientEnergy_eq_ofReal_tsum_norm_sq
    {c : ℤ → ℂ} (hc : Summable fun n : ℤ ↦ ‖c n‖ ^ 2) :
    coefficientEnergy c = ENNReal.ofReal (∑' n : ℤ, ‖c n‖ ^ 2) := by
  unfold coefficientEnergy
  rw [ENNReal.ofReal_tsum_of_nonneg (fun n ↦ sq_nonneg ‖c n‖) hc]

theorem summable_norm_sq_const_mul
    (z : ℂ) {c : ℤ → ℂ}
    (hc : Summable fun n : ℤ ↦ ‖c n‖ ^ 2) :
    Summable fun n : ℤ ↦ ‖z * c n‖ ^ 2 := by
  have hscaled : Summable fun n : ℤ ↦ ‖z‖ ^ 2 * ‖c n‖ ^ 2 :=
    hc.mul_left (‖z‖ ^ 2)
  apply hscaled.congr
  intro n
  rw [norm_mul, mul_pow]

/-- Scalar multiplication retains its exact squared weight. -/
theorem coefficientEnergy_const_mul_le_of_tsum_norm_sq_le
    (z : ℂ) {c : ℤ → ℂ} {C : ℝ}
    (hc : Summable fun n : ℤ ↦ ‖c n‖ ^ 2)
    (hC : (∑' n : ℤ, ‖c n‖ ^ 2) ≤ C) :
    coefficientEnergy (fun n ↦ z * c n) ≤
      ENNReal.ofReal (‖z‖ ^ 2) * ENNReal.ofReal C := by
  have hzc := summable_norm_sq_const_mul z hc
  rw [coefficientEnergy_eq_ofReal_tsum_norm_sq hzc]
  calc
    ENNReal.ofReal (∑' n : ℤ, ‖z * c n‖ ^ 2) =
        ENNReal.ofReal (‖z‖ ^ 2 * (∑' n : ℤ, ‖c n‖ ^ 2)) := by
      congr 1
      calc
        (∑' n : ℤ, ‖z * c n‖ ^ 2) =
            ∑' n : ℤ, ‖z‖ ^ 2 * ‖c n‖ ^ 2 := by
          apply tsum_congr
          intro n
          rw [norm_mul, mul_pow]
        _ = ‖z‖ ^ 2 * (∑' n : ℤ, ‖c n‖ ^ 2) := by
          rw [tsum_mul_left]
    _ ≤ ENNReal.ofReal (‖z‖ ^ 2 * C) :=
      ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left hC (sq_nonneg ‖z‖))
    _ = ENNReal.ofReal (‖z‖ ^ 2) * ENNReal.ofReal C := by
      rw [ENNReal.ofReal_mul (sq_nonneg ‖z‖)]

/-! ## Summability of the literal fixed-away blocks -/

theorem summable_fixedAwayShiftedDyadicTotalSum_norm_sq
    {t δ : ℝ} {N M : ℕ} {ell : ℤ}
    (hδ : 0 < δ) (hδt : δ < t)
    (hN : 0 < N) (hell : ell ≠ 0) :
    Summable fun n : ℤ ↦
      ‖fixedAwayShiftedDyadicTotalSum t δ N M ell n‖ ^ 2 := by
  let P : ℤ → ℂ := fixedAwayShiftedProjectedDyadicSum t δ N M ell
  let E : ℤ → ℂ := fixedAwayShiftedLeakageDyadicSum t δ N M ell
  have hP := summable_fixedAwayShiftedProjectedDyadicSum_norm_sq
    (t := t) (δ := δ) (N := N) (M := M) (ell := ell)
    hδ hδt hN hell
  have hE := summable_fixedAwayShiftedLeakageDyadicSum_norm_sq
    (t := t) (δ := δ) (N := N) (M := M) (ell := ell) hδ hδt
  have hright : Summable fun n : ℤ ↦
      2 * (‖P n‖ ^ 2 + ‖E n‖ ^ 2) :=
    (hP.add hE).mul_left 2
  apply hright.of_nonneg_of_le (fun n ↦ sq_nonneg _)
  intro n
  rw [fixedAwayShiftedDyadicTotalSum_eq_projected_add_leakage]
  change ‖P n + E n‖ ^ 2 ≤ _
  refine (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2).trans ?_
  nlinarith [sq_nonneg (‖P n‖ - ‖E n‖)]

theorem summable_norm_sq_finset_sum
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (c : ι → ℤ → ℂ)
    (hc : ∀ i ∈ S, Summable fun n : ℤ ↦ ‖c i n‖ ^ 2) :
    Summable fun n : ℤ ↦ ‖∑ i ∈ S, c i n‖ ^ 2 := by
  have hright : Summable fun n : ℤ ↦
      (S.card : ℝ) * ∑ i ∈ S, ‖c i n‖ ^ 2 :=
    (summable_sum hc).mul_left (S.card : ℝ)
  apply hright.of_nonneg_of_le (fun n ↦ sq_nonneg _)
  intro n
  refine (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans ?_
  exact sq_sum_le_card_mul_sum_sq

theorem summable_fixedAwayShiftedExponentFinsetSum_norm_sq
    {S : Finset ℕ} {t δ : ℝ} {N : ℕ} {ell : ℤ}
    (hδ : 0 < δ) (hδt : δ < t)
    (hs2 : ∀ s ∈ S, 2 ≤ s) :
    Summable fun n : ℤ ↦
      ‖fixedAwayShiftedExponentFinsetSum S t δ N ell n‖ ^ 2 := by
  simpa only [fixedAwayShiftedExponentFinsetSum] using!
    (summable_norm_sq_finset_sum S
      (fun s ↦ fixedAwayShiftedExponentBlock t δ N ell s)
      (fun s hs ↦ summable_fixedAwayShiftedExponentBlock_norm_sq
        hδ hδt (hs2 s hs)))

theorem summable_fixedAwayShiftedFinitePrefix_norm_sq
    {t δ : ℝ} {N : ℕ} {ell : ℤ}
    (hδ : 0 < δ) (hδt : δ < t) :
    Summable fun n : ℤ ↦
      ‖fixedAwayShiftedFinitePrefix t δ N ell n‖ ^ 2 := by
  have hOne := summable_fixedAwayShiftedSingletonOne_norm_sq
    (N := N) (ell := ell) hδ hδt
  have hTwo := summable_fixedAwayShiftedDyadicBlock_norm_sq
    (N := N) (ell := ell) hδ hδt (by norm_num : 0 < 1)
  have hright : Summable fun n : ℤ ↦
      2 * (‖fixedAwayShiftedSingletonOne t δ N ell n‖ ^ 2 +
        ‖fixedAwayShiftedDyadicBlock t δ N ell 1 n‖ ^ 2) :=
    (hOne.add hTwo).mul_left 2
  apply hright.of_nonneg_of_le (fun n ↦ sq_nonneg _)
  intro n
  unfold fixedAwayShiftedFinitePrefix
  refine (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2).trans ?_
  nlinarith [sq_nonneg
    (‖fixedAwayShiftedSingletonOne t δ N ell n‖ -
      ‖fixedAwayShiftedDyadicBlock t δ N ell 1 n‖)]

/-! ## Weighted finite-carrier aggregation -/

def fixedAwayFiniteNonzeroCarrierSet (K : ℕ) : Finset ℤ :=
  (Finset.Icc (-(K : ℤ)) (K : ℤ)).erase 0

def fixedAwayFiniteNonzeroLowCarrierCoefficients
    (K : ℕ) (t δ : ℝ) (N M : ℕ) (n : ℤ) : ℂ :=
  ∑ ell ∈ fixedAwayFiniteNonzeroCarrierSet K,
    bernoulliMarkFourierCoefficient ell *
      fixedAwayShiftedDyadicTotalSum t δ N M ell n

def fixedAwayFiniteNonzeroHighCarrierCoefficients
    (K : ℕ) (S : Finset ℕ) (t δ : ℝ) (N : ℕ) (n : ℤ) : ℂ :=
  ∑ ell ∈ fixedAwayFiniteNonzeroCarrierSet K,
    bernoulliMarkFourierCoefficient ell *
      fixedAwayShiftedExponentFinsetSum S t δ N ell n

def fixedAwayFiniteNonzeroPrefixCarrierCoefficients
    (K : ℕ) (t δ : ℝ) (N : ℕ) (n : ℤ) : ℂ :=
  ∑ ell ∈ fixedAwayFiniteNonzeroCarrierSet K,
    bernoulliMarkFourierCoefficient ell *
      fixedAwayShiftedFinitePrefix t δ N ell n

def fixedAwayLowCommonEnergyUniformBound
    (T δ R : ℝ) (M J : ℕ) : ℝ :=
  2 * (4 * M * fixedAwayShiftedDyadicEnergyUniformConstant T δ J +
    M ^ 2 * fixedAwayProjectedDyadicEnergyUniformConstant T δ J *
      fixedAwayRapidEnvelope J (R / 4))

def fixedAwayHighCommonEnergyUniformBound
    (T δ : ℝ) (H J : ℕ) : ℝ :=
  H ^ 2 * fixedAwayShiftedDyadicEnergyUniformConstant T δ J

def fixedAwayPrefixCommonEnergyUniformBound
    (T δ : ℝ) (J : ℕ) : ℝ :=
  2 * (fixedAwayShiftedDiagonalUniformConstant T δ +
    fixedAwayShiftedDyadicEnergyUniformConstant T δ J)

private theorem fixedAwayFiniteNonzeroCarrierSet_ne_zero
    {K : ℕ} {ell : ℤ} (hell : ell ∈ fixedAwayFiniteNonzeroCarrierSet K) :
    ell ≠ 0 := by
  exact Finset.ne_of_mem_erase hell

private theorem weightedCarrierMass_le (K : ℕ) :
    (∑ ell ∈ fixedAwayFiniteNonzeroCarrierSet K,
      ‖bernoulliMarkFourierCoefficient ell‖) ≤
      windowCarrierMassConstant := by
  calc
    (∑ ell ∈ fixedAwayFiniteNonzeroCarrierSet K,
        ‖bernoulliMarkFourierCoefficient ell‖) ≤
        ∑ ell ∈ fixedAwayFiniteNonzeroCarrierSet K,
          bernoulliCarrierMajorant ell := by
      gcongr with ell hell
      exact norm_bernoulliMarkFourierCoefficient_le_majorant ell
    _ ≤ windowCarrierMassConstant :=
      sum_bernoulliCarrierMajorant_le _

theorem coefficientEnergy_fixedAwayFiniteNonzeroLowCarrier_le_uniform
    {t δ T R : ℝ} {N M K : ℕ}
    (hδ : 0 < δ) (hδt : δ < t) (htT : t ≤ T)
    (hN : 0 < N) (hR : 0 < R)
    (hcut : ∀ s ∈ nearCarrierDyadicExponents M,
      ((2 ^ s : ℕ) : ℝ) * R ≤ (N : ℝ))
    {J : ℕ} (hJ : 0 < J) :
    coefficientEnergy
        (fixedAwayFiniteNonzeroLowCarrierCoefficients K t δ N M) ≤
      ENNReal.ofReal (windowCarrierMassConstant ^ 2) *
        ENNReal.ofReal (fixedAwayLowCommonEnergyUniformBound T δ R M J) := by
  let S := fixedAwayFiniteNonzeroCarrierSet K
  let w : ℤ → ℝ := fun ell ↦ ‖bernoulliMarkFourierCoefficient ell‖
  let c : ℤ → ℤ → ℂ := fun ell n ↦
    bernoulliMarkFourierCoefficient ell *
      fixedAwayShiftedDyadicTotalSum t δ N M ell n
  let B := ENNReal.ofReal (fixedAwayLowCommonEnergyUniformBound T δ R M J)
  have hcommon := coefficientEnergy_finset_sum_le_weighted_common
    S c w B
    (fun ell _hell ↦ norm_bernoulliMarkFourierCoefficient_pos ell)
    (fun ell hell ↦ by
      have hell0 : ell ≠ 0 := fixedAwayFiniteNonzeroCarrierSet_ne_zero hell
      apply coefficientEnergy_const_mul_le_of_tsum_norm_sq_le
      · exact summable_fixedAwayShiftedDyadicTotalSum_norm_sq
          hδ hδt hN hell0
      · simpa only [fixedAwayLowCommonEnergyUniformBound] using!
          (tsum_fixedAwayShiftedDyadicTotalSum_norm_sq_le_of_cutoff_uniform
            (t := t) (δ := δ) (T := T) (R := R)
            (N := N) (M := M) (ell := ell)
            hδ hδt htT hN hell0 hR hcut hJ))
  have hweight := weightedCarrierMass_le K
  have hsum0 : 0 ≤ ∑ ell ∈ S, w ell :=
    Finset.sum_nonneg fun ell _hell ↦ norm_nonneg _
  have hmass0 := windowCarrierMassConstant_nonneg
  calc
    coefficientEnergy
        (fixedAwayFiniteNonzeroLowCarrierCoefficients K t δ N M) ≤
        ENNReal.ofReal ((∑ ell ∈ S, w ell) ^ 2) * B := by
      simpa only [fixedAwayFiniteNonzeroLowCarrierCoefficients, S, c, w, B]
        using! hcommon
    _ ≤ ENNReal.ofReal (windowCarrierMassConstant ^ 2) * B := by
      gcongr
    _ = ENNReal.ofReal (windowCarrierMassConstant ^ 2) *
        ENNReal.ofReal (fixedAwayLowCommonEnergyUniformBound T δ R M J) := rfl

theorem coefficientEnergy_fixedAwayFiniteNonzeroHighCarrier_le_uniform
    {S : Finset ℕ} {t δ T : ℝ} {N K : ℕ}
    (hδ : 0 < δ) (hδt : δ < t) (htT : t ≤ T)
    (hs2 : ∀ s ∈ S, 2 ≤ s)
    {J : ℕ} (hJ : 0 < J) :
    coefficientEnergy
        (fixedAwayFiniteNonzeroHighCarrierCoefficients K S t δ N) ≤
      ENNReal.ofReal (windowCarrierMassConstant ^ 2) *
        ENNReal.ofReal
          (fixedAwayHighCommonEnergyUniformBound T δ S.card J) := by
  let E := fixedAwayFiniteNonzeroCarrierSet K
  let w : ℤ → ℝ := fun ell ↦ ‖bernoulliMarkFourierCoefficient ell‖
  let c : ℤ → ℤ → ℂ := fun ell n ↦
    bernoulliMarkFourierCoefficient ell *
      fixedAwayShiftedExponentFinsetSum S t δ N ell n
  let B := ENNReal.ofReal
    (fixedAwayHighCommonEnergyUniformBound T δ S.card J)
  have hcommon := coefficientEnergy_finset_sum_le_weighted_common
    E c w B
    (fun ell _hell ↦ norm_bernoulliMarkFourierCoefficient_pos ell)
    (fun ell _hell ↦ by
      apply coefficientEnergy_const_mul_le_of_tsum_norm_sq_le
      · exact summable_fixedAwayShiftedExponentFinsetSum_norm_sq
          hδ hδt hs2
      · simpa only [fixedAwayHighCommonEnergyUniformBound] using!
          (tsum_fixedAwayShiftedExponentFinsetSum_norm_sq_le_uniform
            (S := S) (t := t) (δ := δ) (T := T)
            (N := N) (ell := ell) hδ hδt htT hs2 hJ))
  have hweight := weightedCarrierMass_le K
  have hsum0 : 0 ≤ ∑ ell ∈ E, w ell :=
    Finset.sum_nonneg fun ell _hell ↦ norm_nonneg _
  have hmass0 := windowCarrierMassConstant_nonneg
  calc
    coefficientEnergy
        (fixedAwayFiniteNonzeroHighCarrierCoefficients K S t δ N) ≤
        ENNReal.ofReal ((∑ ell ∈ E, w ell) ^ 2) * B := by
      simpa only [fixedAwayFiniteNonzeroHighCarrierCoefficients, E, c, w, B]
        using! hcommon
    _ ≤ ENNReal.ofReal (windowCarrierMassConstant ^ 2) * B := by
      gcongr
    _ = ENNReal.ofReal (windowCarrierMassConstant ^ 2) *
        ENNReal.ofReal
          (fixedAwayHighCommonEnergyUniformBound T δ S.card J) := rfl

theorem coefficientEnergy_fixedAwayFiniteNonzeroPrefixCarrier_le_uniform
    {t δ T : ℝ} {N K : ℕ}
    (hδ : 0 < δ) (hδt : δ < t) (htT : t ≤ T)
    {J : ℕ} (hJ : 0 < J) :
    coefficientEnergy
        (fixedAwayFiniteNonzeroPrefixCarrierCoefficients K t δ N) ≤
      ENNReal.ofReal (windowCarrierMassConstant ^ 2) *
        ENNReal.ofReal (fixedAwayPrefixCommonEnergyUniformBound T δ J) := by
  let E := fixedAwayFiniteNonzeroCarrierSet K
  let w : ℤ → ℝ := fun ell ↦ ‖bernoulliMarkFourierCoefficient ell‖
  let c : ℤ → ℤ → ℂ := fun ell n ↦
    bernoulliMarkFourierCoefficient ell *
      fixedAwayShiftedFinitePrefix t δ N ell n
  let B := ENNReal.ofReal (fixedAwayPrefixCommonEnergyUniformBound T δ J)
  have hcommon := coefficientEnergy_finset_sum_le_weighted_common
    E c w B
    (fun ell _hell ↦ norm_bernoulliMarkFourierCoefficient_pos ell)
    (fun ell _hell ↦ by
      apply coefficientEnergy_const_mul_le_of_tsum_norm_sq_le
      · exact summable_fixedAwayShiftedFinitePrefix_norm_sq hδ hδt
      · simpa only [fixedAwayPrefixCommonEnergyUniformBound] using!
          (tsum_fixedAwayShiftedFinitePrefix_norm_sq_le_uniform
            (t := t) (δ := δ) (T := T) (N := N) (ell := ell)
            hδ hδt htT hJ))
  have hweight := weightedCarrierMass_le K
  have hsum0 : 0 ≤ ∑ ell ∈ E, w ell :=
    Finset.sum_nonneg fun ell _hell ↦ norm_nonneg _
  have hmass0 := windowCarrierMassConstant_nonneg
  calc
    coefficientEnergy
        (fixedAwayFiniteNonzeroPrefixCarrierCoefficients K t δ N) ≤
        ENNReal.ofReal ((∑ ell ∈ E, w ell) ^ 2) * B := by
      simpa only [fixedAwayFiniteNonzeroPrefixCarrierCoefficients, E, c, w, B]
        using! hcommon
    _ ≤ ENNReal.ofReal (windowCarrierMassConstant ^ 2) * B := by
      gcongr
    _ = ENNReal.ofReal (windowCarrierMassConstant ^ 2) *
        ENNReal.ofReal (fixedAwayPrefixCommonEnergyUniformBound T δ J) := rfl

end

end Erdos1002
