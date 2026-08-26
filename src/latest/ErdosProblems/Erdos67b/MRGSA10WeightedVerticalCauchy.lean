import ErdosProblems.Erdos67b.MRGSA10MovingKernelRpow
import ErdosProblems.Erdos67b.MRGSA10VerticalCauchy

/-!
# Perron-weighted vertical Cauchy--Schwarz

This file retains one power of the Perron denominator in each square
energy.  A dyadic shell argument converts a cumulative symmetric energy
bound `E₀ + E₁ R` into an explicit logarithmic number of shell costs.
-/

open scoped BigOperators ENNReal
open Complex MeasureTheory Set

namespace Erdos67b.MRHalaszBands

noncomputable section

/-- The norm of the reciprocal vertical Perron denominator. -/
def gsA10VerticalPerronWeight (sigma t : ℝ) : ℝ :=
  (Real.sqrt (sigma ^ 2 + t ^ 2))⁻¹

/-- One-denominator square energy on an oriented interval. -/
def gsA10WeightedVerticalEnergy
    (F : ℝ → ℂ) (sigma A B : ℝ) : ℝ :=
  ∫ t in A..B, gsA10VerticalPerronWeight sigma t * Complex.normSq (F t)

theorem gsA10VerticalPerronWeight_nonneg (sigma t : ℝ) :
    0 ≤ gsA10VerticalPerronWeight sigma t := by
  unfold gsA10VerticalPerronWeight
  positivity

theorem continuous_gsA10VerticalPerronWeight
    {sigma : ℝ} (hsigma : 0 < sigma) :
    Continuous (gsA10VerticalPerronWeight sigma) := by
  unfold gsA10VerticalPerronWeight
  apply Continuous.inv₀
  · fun_prop
  · intro t ht
    have hrad : 0 < sigma ^ 2 + t ^ 2 := by
      nlinarith [sq_pos_of_pos hsigma, sq_nonneg t]
    exact (Real.sqrt_pos.2 hrad).ne' ht

theorem continuous_gsA10WeightedVerticalIntegrand
    (F : ℝ → ℂ) (hF : Continuous F)
    {sigma : ℝ} (hsigma : 0 < sigma) :
    Continuous (fun t ↦
      gsA10VerticalPerronWeight sigma t * Complex.normSq (F t)) := by
  exact (continuous_gsA10VerticalPerronWeight hsigma).mul
    (Complex.continuous_normSq.comp hF)

/-- In the central band the reciprocal denominator costs at most two. -/
theorem gsA10VerticalPerronWeight_le_two
    {sigma : ℝ} (hsigma : 1 / 2 ≤ sigma) (t : ℝ) :
    gsA10VerticalPerronWeight sigma t ≤ 2 := by
  have hsigmaPos : 0 < sigma :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le hsigma
  have hrad : 0 ≤ sigma ^ 2 + t ^ 2 := by positivity
  have hsqrt : (1 / 2 : ℝ) ≤ Real.sqrt (sigma ^ 2 + t ^ 2) := by
    rw [Real.le_sqrt (by norm_num) hrad]
    nlinarith [sq_nonneg t]
  unfold gsA10VerticalPerronWeight
  have hinv := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) hsqrt
  norm_num at hinv ⊢
  exact hinv

/-- On a shell `R ≤ |t|`, the reciprocal denominator is at most `R⁻¹`. -/
theorem gsA10VerticalPerronWeight_le_inv
    {sigma R t : ℝ} (hsigma : 0 < sigma) (hR : 0 < R)
    (ht : R ≤ |t|) :
    gsA10VerticalPerronWeight sigma t ≤ R⁻¹ := by
  have hrad : 0 ≤ sigma ^ 2 + t ^ 2 := by positivity
  have htSq : R ^ 2 ≤ t ^ 2 := by
    nlinarith [abs_nonneg t, sq_abs t]
  have hsqrt : R ≤ Real.sqrt (sigma ^ 2 + t ^ 2) := by
    rw [Real.le_sqrt hR.le hrad]
    nlinarith [sq_nonneg sigma]
  unfold gsA10VerticalPerronWeight
  exact inv_anti₀ hR hsqrt

/-- Central interval plus its first `K` positive and negative dyadic shells. -/
def gsA10SymmetricDyadicIntegral (G : ℝ → ℝ) (K : ℕ) : ℝ :=
  (∫ t in (-1 : ℝ)..1, G t) +
    ∑ j ∈ Finset.range K,
      ((∫ t in -(((2 : ℕ) ^ (j + 1) : ℕ) : ℝ)..
          -(((2 : ℕ) ^ j : ℕ) : ℝ), G t) +
        ∫ t in (((2 : ℕ) ^ j : ℕ) : ℝ)..
          (((2 : ℕ) ^ (j + 1) : ℕ) : ℝ), G t)

/-- Exact reconstruction of a symmetric dyadic interval. -/
theorem gsA10SymmetricDyadicIntegral_eq
    (G : ℝ → ℝ) (hG : Continuous G) (K : ℕ) :
    gsA10SymmetricDyadicIntegral G K =
      ∫ t in -(((2 : ℕ) ^ K : ℕ) : ℝ)..
        (((2 : ℕ) ^ K : ℕ) : ℝ), G t := by
  induction K with
  | zero => simp [gsA10SymmetricDyadicIntegral]
  | succ K ih =>
      rw [gsA10SymmetricDyadicIntegral, Finset.sum_range_succ]
      rw [← add_assoc]
      change gsA10SymmetricDyadicIntegral G K + _ = _
      rw [ih]
      let A : ℝ := (((2 : ℕ) ^ K : ℕ) : ℝ)
      let B : ℝ := (((2 : ℕ) ^ (K + 1) : ℕ) : ℝ)
      have hneg : IntervalIntegrable G volume (-B) (-A) :=
        hG.intervalIntegrable _ _
      have hmid : IntervalIntegrable G volume (-A) A :=
        hG.intervalIntegrable _ _
      have hpos : IntervalIntegrable G volume A B :=
        hG.intervalIntegrable _ _
      have hleft :=
        intervalIntegral.integral_add_adjacent_intervals hneg hmid
      have hright := intervalIntegral.integral_add_adjacent_intervals
        (hG.intervalIntegrable (-B) A) hpos
      dsimp only [A, B] at hleft hright
      rw [show K + 1 = Nat.succ K by omega]
      rw [← add_assoc]
      rw [add_comm
        (∫ t in -(((2 : ℕ) ^ K : ℕ) : ℝ)..
            (((2 : ℕ) ^ K : ℕ) : ℝ), G t)
        (∫ t in -(((2 : ℕ) ^ (K + 1) : ℕ) : ℝ)..
            -(((2 : ℕ) ^ K : ℕ) : ℝ), G t)]
      rw [hleft, hright]

private theorem sum_inv_two_pow_le_two (K : ℕ) :
    (∑ j ∈ Finset.range K, ((((2 : ℕ) ^ j : ℕ) : ℝ))⁻¹) ≤ 2 := by
  have hs := summable_geometric_of_lt_one
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  calc
    (∑ j ∈ Finset.range K, ((((2 : ℕ) ^ j : ℕ) : ℝ))⁻¹) =
        ∑ j ∈ Finset.range K, (1 / 2 : ℝ) ^ j := by
      apply Finset.sum_congr rfl
      intro j hj
      push_cast
      rw [← inv_pow]
      norm_num
    _ ≤ ∑' j : ℕ, (1 / 2 : ℝ) ^ j :=
      hs.sum_le_tsum (Finset.range K)
        (fun j hj ↦ pow_nonneg (by norm_num) j)
    _ = 2 := by
      rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      norm_num

/-- Dyadic-shell form of the weighted-energy estimate.  The cumulative
hypothesis is required only up to the chosen outer dyadic radius `2^K`. -/
theorem gsA10WeightedVerticalEnergy_dyadic_le
    (F : ℝ → ℂ) (hF : Continuous F)
    {sigma E₀ E₁ : ℝ} (hsigma : 1 / 2 ≤ sigma)
    (hE₀ : 0 ≤ E₀) (_hE₁ : 0 ≤ E₁) (K : ℕ)
    (henergy : ∀ R : ℝ, 1 ≤ R →
      R ≤ (((2 : ℕ) ^ K : ℕ) : ℝ) →
      (∫ t in -R..R, Complex.normSq (F t)) ≤ E₀ + E₁ * R) :
    gsA10WeightedVerticalEnergy F sigma
        (-(((2 : ℕ) ^ K : ℕ) : ℝ))
        (((2 : ℕ) ^ K : ℕ) : ℝ) ≤
      6 * E₀ + (2 + 4 * K) * E₁ := by
  let G : ℝ → ℝ := fun t ↦ Complex.normSq (F t)
  let W : ℝ → ℝ := fun t ↦
    gsA10VerticalPerronWeight sigma t * G t
  have hsigmaPos : 0 < sigma :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le hsigma
  have hG : Continuous G := Complex.continuous_normSq.comp hF
  have hW : Continuous W := by
    exact (continuous_gsA10VerticalPerronWeight hsigmaPos).mul hG
  have hGnonneg : ∀ t, 0 ≤ G t := fun t ↦ Complex.normSq_nonneg _
  have hcentral : (∫ t in (-1 : ℝ)..1, W t) ≤
      2 * (E₀ + E₁) := by
    calc
      (∫ t in (-1 : ℝ)..1, W t) ≤
          ∫ t in (-1 : ℝ)..1, 2 * G t := by
        apply intervalIntegral.integral_mono_on (by norm_num)
        · exact hW.intervalIntegrable _ _
        · exact (hG.const_mul 2).intervalIntegrable _ _
        · intro t ht
          dsimp only [W]
          exact mul_le_mul_of_nonneg_right
            (gsA10VerticalPerronWeight_le_two hsigma t) (hGnonneg t)
      _ = 2 * ∫ t in (-1 : ℝ)..1, G t := by
        rw [intervalIntegral.integral_const_mul]
      _ ≤ 2 * (E₀ + E₁) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        simpa only [G, mul_one] using henergy 1 (by norm_num)
          (by exact_mod_cast (one_le_pow₀ (by omega) : 1 ≤ 2 ^ K))
  have hshell : ∀ j < K,
      ((∫ t in -(((2 : ℕ) ^ (j + 1) : ℕ) : ℝ)..
          -(((2 : ℕ) ^ j : ℕ) : ℝ), W t) +
        ∫ t in (((2 : ℕ) ^ j : ℕ) : ℝ)..
          (((2 : ℕ) ^ (j + 1) : ℕ) : ℝ), W t) ≤
      2 * E₀ * ((((2 : ℕ) ^ j : ℕ) : ℝ))⁻¹ + 4 * E₁ := by
    intro j hj
    let r : ℝ := (((2 : ℕ) ^ j : ℕ) : ℝ)
    let R : ℝ := (((2 : ℕ) ^ (j + 1) : ℕ) : ℝ)
    have hr : 0 < r := by dsimp only [r]; positivity
    have hrR : r ≤ R := by
      dsimp only [r, R]
      exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < 2) (by omega)
    have hRone : 1 ≤ R := by
      dsimp only [R]
      exact_mod_cast (one_le_pow₀ (by omega) : 1 ≤ 2 ^ (j + 1))
    have hRK : R ≤ (((2 : ℕ) ^ K : ℕ) : ℝ) := by
      have hjK : j + 1 ≤ K := by omega
      have hp : 2 ^ (j + 1) ≤ 2 ^ K :=
        Nat.pow_le_pow_right (by omega : 0 < 2) hjK
      dsimp only [R]
      exact_mod_cast hp
    have hfull := henergy R hRone hRK
    change (∫ t in -R..R, G t) ≤ E₀ + E₁ * R at hfull
    have hfullInt : IntervalIntegrable G volume (-R) R :=
      hG.intervalIntegrable _ _
    have hGae : 0 ≤ᵐ[volume.restrict (Set.Ioc (-R) R)] G :=
      ae_restrict_of_forall_mem measurableSet_Ioc fun t ht ↦ hGnonneg t
    have hnegG : (∫ t in -R..-r, G t) ≤ ∫ t in -R..R, G t := by
      exact intervalIntegral.integral_mono_interval le_rfl (by linarith)
        (by linarith) hGae hfullInt
    have hposG : (∫ t in r..R, G t) ≤ ∫ t in -R..R, G t := by
      exact intervalIntegral.integral_mono_interval (by linarith) hrR le_rfl
        hGae hfullInt
    have hshellG : (∫ t in -R..-r, G t) + (∫ t in r..R, G t) ≤
        2 * (E₀ + E₁ * R) := by linarith
    have hnegW : (∫ t in -R..-r, W t) ≤
        r⁻¹ * ∫ t in -R..-r, G t := by
      calc
        (∫ t in -R..-r, W t) ≤ ∫ t in -R..-r, r⁻¹ * G t := by
          apply intervalIntegral.integral_mono_on (by linarith)
          · exact hW.intervalIntegrable _ _
          · exact (hG.const_mul r⁻¹).intervalIntegrable _ _
          · intro t ht
            dsimp only [W]
            apply mul_le_mul_of_nonneg_right _ (hGnonneg t)
            apply gsA10VerticalPerronWeight_le_inv hsigmaPos hr
            have ht0 : t ≤ 0 := ht.2.trans (neg_nonpos.mpr hr.le)
            rw [abs_of_nonpos ht0]
            linarith [ht.2]
        _ = r⁻¹ * ∫ t in -R..-r, G t := by
          rw [intervalIntegral.integral_const_mul]
    have hposW : (∫ t in r..R, W t) ≤
        r⁻¹ * ∫ t in r..R, G t := by
      calc
        (∫ t in r..R, W t) ≤ ∫ t in r..R, r⁻¹ * G t := by
          apply intervalIntegral.integral_mono_on hrR
          · exact hW.intervalIntegrable _ _
          · exact (hG.const_mul r⁻¹).intervalIntegrable _ _
          · intro t ht
            dsimp only [W]
            apply mul_le_mul_of_nonneg_right _ (hGnonneg t)
            apply gsA10VerticalPerronWeight_le_inv hsigmaPos hr
            have ht0 : 0 ≤ t := hr.le.trans ht.1
            rw [abs_of_nonneg ht0]
            exact ht.1
        _ = r⁻¹ * ∫ t in r..R, G t := by
          rw [intervalIntegral.integral_const_mul]
    have hscaled : r⁻¹ *
        ((∫ t in -R..-r, G t) + (∫ t in r..R, G t)) ≤
        r⁻¹ * (2 * (E₀ + E₁ * R)) :=
      mul_le_mul_of_nonneg_left hshellG (inv_nonneg.mpr hr.le)
    have hR : R = 2 * r := by
      dsimp only [R, r]
      push_cast
      rw [pow_succ]
      ring
    have hbudget : r⁻¹ * (2 * (E₀ + E₁ * R)) =
        2 * E₀ * r⁻¹ + 4 * E₁ := by
      rw [hR]
      field_simp [ne_of_gt hr]
      ring
    dsimp only [R, r] at hnegW hposW ⊢
    calc
      _ ≤ ((((2 : ℕ) ^ j : ℕ) : ℝ))⁻¹ *
          ((∫ t in -(((2 : ℕ) ^ (j + 1) : ℕ) : ℝ)..
              -(((2 : ℕ) ^ j : ℕ) : ℝ), G t) +
            ∫ t in (((2 : ℕ) ^ j : ℕ) : ℝ)..
              (((2 : ℕ) ^ (j + 1) : ℕ) : ℝ), G t) := by
        linarith
      _ ≤ ((((2 : ℕ) ^ j : ℕ) : ℝ))⁻¹ *
          (2 * (E₀ + E₁ * (((2 : ℕ) ^ (j + 1) : ℕ) : ℝ))) := by
        exact hscaled
      _ = _ := hbudget
  have hshellSum :
      (∑ j ∈ Finset.range K,
        ((∫ t in -(((2 : ℕ) ^ (j + 1) : ℕ) : ℝ)..
            -(((2 : ℕ) ^ j : ℕ) : ℝ), W t) +
          ∫ t in (((2 : ℕ) ^ j : ℕ) : ℝ)..
            (((2 : ℕ) ^ (j + 1) : ℕ) : ℝ), W t)) ≤
        4 * E₀ + 4 * K * E₁ := by
    calc
      _ ≤ ∑ j ∈ Finset.range K,
          (2 * E₀ * ((((2 : ℕ) ^ j : ℕ) : ℝ))⁻¹ + 4 * E₁) := by
        apply Finset.sum_le_sum
        intro j hj
        exact hshell j (Finset.mem_range.mp hj)
      _ = 2 * E₀ *
            (∑ j ∈ Finset.range K, ((((2 : ℕ) ^ j : ℕ) : ℝ))⁻¹) +
          K * (4 * E₁) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ 2 * E₀ * 2 + K * (4 * E₁) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (sum_inv_two_pow_le_two K)
            (show 0 ≤ 2 * E₀ by positivity)) le_rfl
      _ = 4 * E₀ + 4 * K * E₁ := by ring
  unfold gsA10WeightedVerticalEnergy
  change (∫ t in -(((2 : ℕ) ^ K : ℕ) : ℝ)..
    (((2 : ℕ) ^ K : ℕ) : ℝ), W t) ≤ _
  rw [← gsA10SymmetricDyadicIntegral_eq W hW K]
  unfold gsA10SymmetricDyadicIntegral
  calc
    _ ≤ 2 * (E₀ + E₁) + (4 * E₀ + 4 * K * E₁) :=
      add_le_add hcentral hshellSum
    _ = 6 * E₀ + (2 + 4 * K) * E₁ := by ring

/-- A truncated interval lying inside the outer dyadic radius satisfies the
same explicit finite-log bound. -/
theorem gsA10WeightedVerticalEnergy_le_of_dyadic_cumulative
    (F : ℝ → ℂ) (hF : Continuous F)
    {sigma E₀ E₁ T : ℝ} (hsigma : 1 / 2 ≤ sigma)
    (hE₀ : 0 ≤ E₀) (hE₁ : 0 ≤ E₁) (hT : 0 ≤ T)
    (K : ℕ) (hTK : T ≤ (((2 : ℕ) ^ K : ℕ) : ℝ))
    (henergy : ∀ R : ℝ, 1 ≤ R →
      R ≤ (((2 : ℕ) ^ K : ℕ) : ℝ) →
      (∫ t in -R..R, Complex.normSq (F t)) ≤ E₀ + E₁ * R) :
    gsA10WeightedVerticalEnergy F sigma (-T) T ≤
      6 * E₀ + (2 + 4 * K) * E₁ := by
  have hsigmaPos : 0 < sigma :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le hsigma
  let W : ℝ → ℝ := fun t ↦
    gsA10VerticalPerronWeight sigma t * Complex.normSq (F t)
  have hW : Continuous W :=
    (continuous_gsA10VerticalPerronWeight hsigmaPos).mul
      (Complex.continuous_normSq.comp hF)
  have hWnonneg : ∀ t, 0 ≤ W t := fun t ↦
    mul_nonneg (gsA10VerticalPerronWeight_nonneg _ _)
      (Complex.normSq_nonneg _)
  have houterInt : IntervalIntegrable W volume
      (-(((2 : ℕ) ^ K : ℕ) : ℝ))
      (((2 : ℕ) ^ K : ℕ) : ℝ) := hW.intervalIntegrable _ _
  have hmono : (∫ t in -T..T, W t) ≤
      ∫ t in -(((2 : ℕ) ^ K : ℕ) : ℝ)..
        (((2 : ℕ) ^ K : ℕ) : ℝ), W t := by
    apply intervalIntegral.integral_mono_interval
      (by linarith) (by linarith) hTK
    · exact ae_restrict_of_forall_mem measurableSet_Ioc
        (fun t ht ↦ hWnonneg t)
    · exact houterInt
  exact hmono.trans
    (gsA10WeightedVerticalEnergy_dyadic_le
      F hF hsigma hE₀ hE₁ K henergy)

/-- Weighted Cauchy--Schwarz with one half of the Perron denominator placed
in each square energy. -/
theorem norm_intervalIntegral_mul_div_vertical_le_weightedEnergy
    (A B : ℝ → ℂ) (hA : Continuous A) (hB : Continuous B)
    {sigma T : ℝ} (hsigma : 1 / 2 ≤ sigma) (hT : 0 ≤ T) :
    ‖∫ t in -T..T,
        A t * B t / ((sigma : ℂ) + I * (t : ℂ))‖ ≤
      (gsA10WeightedVerticalEnergy A sigma (-T) T) ^ ((1 : ℝ) / 2) *
        (gsA10WeightedVerticalEnergy B sigma (-T) T) ^ ((1 : ℝ) / 2) := by
  let S : Set ℝ := Set.Ioc (-T) T
  let w : ℝ → ℝ := fun t ↦ gsA10VerticalPerronWeight sigma t
  let u : ℝ → ℝ := fun t ↦ ‖A t‖ * Real.sqrt (w t)
  let v : ℝ → ℝ := fun t ↦ ‖B t‖ * Real.sqrt (w t)
  have hsigmaPos : 0 < sigma :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le hsigma
  have hw : Continuous w := continuous_gsA10VerticalPerronWeight hsigmaPos
  have hu : Continuous u := hA.norm.mul (Real.continuous_sqrt.comp hw)
  have hv : Continuous v := hB.norm.mul (Real.continuous_sqrt.comp hw)
  have huLp : MemLp u 2 (volume.restrict S) := by
    apply (memLp_two_iff_integrable_sq hu.aestronglyMeasurable).2
    exact (hu.pow 2).integrableOn_Ioc
  have hvLp : MemLp v 2 (volume.restrict S) := by
    apply (memLp_two_iff_integrable_sq hv.aestronglyMeasurable).2
    exact (hv.pow 2).integrableOn_Ioc
  have huLp' : MemLp u (ENNReal.ofReal (2 : ℝ)) (volume.restrict S) := by
    simpa using huLp
  have hvLp' : MemLp v (ENNReal.ofReal (2 : ℝ)) (volume.restrict S) := by
    simpa using hvLp
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := volume.restrict S) (f := u) (g := v)
    Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun t ↦
      mul_nonneg (norm_nonneg (A t)) (Real.sqrt_nonneg _))
    (Filter.Eventually.of_forall fun t ↦
      mul_nonneg (norm_nonneg (B t)) (Real.sqrt_nonneg _))
    huLp' hvLp'
  have horder : -T ≤ T := by linarith
  have hholder' :
      (∫ t in -T..T, u t * v t) ≤
        ((∫ t in -T..T, u t ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)) *
          ((∫ t in -T..T, v t ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)) := by
    simpa only [S, ← intervalIntegral.integral_of_le horder] using hholder
  have hdenNorm (t : ℝ) :
      ‖(sigma : ℂ) + I * (t : ℂ)‖ =
        Real.sqrt (sigma ^ 2 + t ^ 2) := by
    rw [Complex.norm_def]
    congr 1
    simp [Complex.normSq_apply]
    ring
  have hsne (t : ℝ) : (sigma : ℂ) + I * (t : ℂ) ≠ 0 := by
    intro ht
    have hre := congrArg Complex.re ht
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul,
      one_mul, sub_zero, Complex.zero_re] at hre
    linarith
  have hquot : Continuous (fun t : ℝ ↦
      A t * B t / ((sigma : ℂ) + I * (t : ℂ))) := by
    apply (hA.mul hB).div
    · fun_prop
    · exact hsne
  have hpoint (t : ℝ) :
      ‖A t * B t / ((sigma : ℂ) + I * (t : ℂ))‖ = u t * v t := by
    have hw0 : 0 ≤ w t := by
      dsimp only [w]
      exact gsA10VerticalPerronWeight_nonneg _ _
    rw [norm_div, norm_mul, hdenNorm]
    calc
      ‖A t‖ * ‖B t‖ / Real.sqrt (sigma ^ 2 + t ^ 2) =
          (‖A t‖ * ‖B t‖) * w t := by
        simp only [w, gsA10VerticalPerronWeight, div_eq_mul_inv]
      _ = u t * v t := by
        dsimp only [u, v]
        have hsqrt : Real.sqrt (w t) * Real.sqrt (w t) = w t :=
          Real.mul_self_sqrt hw0
        calc
          (‖A t‖ * ‖B t‖) * w t =
              (‖A t‖ * ‖B t‖) *
                (Real.sqrt (w t) * Real.sqrt (w t)) := by rw [hsqrt]
          _ = (‖A t‖ * Real.sqrt (w t)) *
              (‖B t‖ * Real.sqrt (w t)) := by ring
  have huEnergy : (∫ t in -T..T, u t ^ (2 : ℝ)) =
      gsA10WeightedVerticalEnergy A sigma (-T) T := by
    unfold gsA10WeightedVerticalEnergy
    apply intervalIntegral.integral_congr
    intro t ht
    have hw0 : 0 ≤ w t := by
      dsimp only [w]
      exact gsA10VerticalPerronWeight_nonneg _ _
    dsimp only [u]
    rw [Real.rpow_two, mul_pow, Real.sq_sqrt hw0,
      Complex.normSq_eq_norm_sq]
    dsimp only [w]
    ring
  have hvEnergy : (∫ t in -T..T, v t ^ (2 : ℝ)) =
      gsA10WeightedVerticalEnergy B sigma (-T) T := by
    unfold gsA10WeightedVerticalEnergy
    apply intervalIntegral.integral_congr
    intro t ht
    have hw0 : 0 ≤ w t := by
      dsimp only [w]
      exact gsA10VerticalPerronWeight_nonneg _ _
    dsimp only [v]
    rw [Real.rpow_two, mul_pow, Real.sq_sqrt hw0,
      Complex.normSq_eq_norm_sq]
    dsimp only [w]
    ring
  calc
    ‖∫ t in -T..T,
        A t * B t / ((sigma : ℂ) + I * (t : ℂ))‖ ≤
        ∫ t in -T..T,
          ‖A t * B t / ((sigma : ℂ) + I * (t : ℂ))‖ :=
      intervalIntegral.norm_integral_le_integral_norm horder
    _ = ∫ t in -T..T, u t * v t := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact hpoint t
    _ ≤ ((∫ t in -T..T, u t ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)) *
          ((∫ t in -T..T, v t ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)) := hholder'
    _ = _ := by rw [huEnergy, hvEnergy]

/-- Numerical consumer form of weighted vertical Cauchy--Schwarz. -/
theorem norm_intervalIntegral_mul_div_vertical_le_of_weightedEnergy
    (A B : ℝ → ℂ) (hA : Continuous A) (hB : Continuous B)
    {sigma T E_A E_B : ℝ} (hsigma : 1 / 2 ≤ sigma) (hT : 0 ≤ T)
    (hEA0 : 0 ≤ E_A) (_hEB0 : 0 ≤ E_B)
    (hEA : gsA10WeightedVerticalEnergy A sigma (-T) T ≤ E_A)
    (hEB : gsA10WeightedVerticalEnergy B sigma (-T) T ≤ E_B) :
    ‖∫ t in -T..T,
        A t * B t / ((sigma : ℂ) + I * (t : ℂ))‖ ≤
      E_A ^ ((1 : ℝ) / 2) * E_B ^ ((1 : ℝ) / 2) := by
  have horder : -T ≤ T := by linarith
  have hbase := norm_intervalIntegral_mul_div_vertical_le_weightedEnergy
    A B hA hB hsigma hT
  have hAE : 0 ≤ gsA10WeightedVerticalEnergy A sigma (-T) T := by
    unfold gsA10WeightedVerticalEnergy
    exact intervalIntegral.integral_nonneg horder
      (fun t ht ↦ mul_nonneg
        (gsA10VerticalPerronWeight_nonneg _ _)
        (Complex.normSq_nonneg _))
  have hBE : 0 ≤ gsA10WeightedVerticalEnergy B sigma (-T) T := by
    unfold gsA10WeightedVerticalEnergy
    exact intervalIntegral.integral_nonneg horder
      (fun t ht ↦ mul_nonneg
        (gsA10VerticalPerronWeight_nonneg _ _)
        (Complex.normSq_nonneg _))
  have hAsqrt := Real.rpow_le_rpow hAE hEA (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hBsqrt := Real.rpow_le_rpow hBE hEB (by norm_num : (0 : ℝ) ≤ 1 / 2)
  exact hbase.trans (mul_le_mul hAsqrt hBsqrt
    (Real.rpow_nonneg hBE _) (Real.rpow_nonneg hEA0 _))

end

end Erdos67b.MRHalaszBands

#print axioms
  Erdos67b.MRHalaszBands.gsA10WeightedVerticalEnergy_dyadic_le
#print axioms
  Erdos67b.MRHalaszBands.gsA10WeightedVerticalEnergy_le_of_dyadic_cumulative
#print axioms
  Erdos67b.MRHalaszBands.norm_intervalIntegral_mul_div_vertical_le_weightedEnergy
#print axioms
  Erdos67b.MRHalaszBands.norm_intervalIntegral_mul_div_vertical_le_of_weightedEnergy
