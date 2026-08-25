import ErdosProblems.Erdos67.MRGSA10HigherPrimePowerMass
import ErdosProblems.Erdos67.MRGSA10SecondaryCoefficientMajorant

/-!
# The higher-prime-power part of the second A.10 secondary sum

For a merely multiplicative coefficient, its generalized Mangoldt function
need not equal `f(n) Λ(n)` at higher prime powers.  This file keeps that
part separate, reindexes the finite convolution prefix, and charges it to
the geometric mass proved in `MRGSA10HigherPrimePowerMass`.
-/

open scoped BigOperators
open Finset Set MeasureTheory

namespace Erdos67.MRHalaszBands

noncomputable section

private def gsPositiveBelow (x : ℕ) : Finset ℕ := Finset.Ico 1 x

private theorem divisors_eq_gsPositiveBelow_filter_dvd {x n : ℕ}
    (hn : n ∈ gsPositiveBelow x) :
    n.divisors = (gsPositiveBelow x).filter fun d ↦ d ∣ n := by
  ext d
  have hnPos : 0 < n := (Finset.mem_Ico.mp hn).1
  have hnLt : n < x := (Finset.mem_Ico.mp hn).2
  simp only [Nat.mem_divisors, Finset.mem_filter, gsPositiveBelow,
    Finset.mem_Ico]
  constructor
  · rintro ⟨hd, hn0⟩
    have hdPos : 0 < d := Nat.pos_of_dvd_of_pos hd hnPos
    exact ⟨⟨hdPos, (Nat.le_of_dvd hnPos hd).trans_lt hnLt⟩, hd⟩
  · rintro ⟨⟨_, _⟩, hd⟩
    exact ⟨hd, Nat.ne_of_gt hnPos⟩

private theorem sum_divisors_reindex_real
    (x : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ n ∈ gsPositiveBelow x, ∑ d ∈ n.divisors, F n d) =
      ∑ d ∈ gsPositiveBelow x,
        ∑ m ∈ (gsPositiveBelow x).filter (fun m ↦ d * m < x),
          F (d * m) d := by
  classical
  calc
    (∑ n ∈ gsPositiveBelow x, ∑ d ∈ n.divisors, F n d) =
        ∑ n ∈ gsPositiveBelow x,
          ∑ d ∈ (gsPositiveBelow x).filter (fun d ↦ d ∣ n), F n d := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [divisors_eq_gsPositiveBelow_filter_dvd hn]
    _ = ∑ d ∈ gsPositiveBelow x,
          ∑ n ∈ (gsPositiveBelow x).filter (fun n ↦ d ∣ n), F n d := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
    _ = ∑ d ∈ gsPositiveBelow x,
          ∑ m ∈ (gsPositiveBelow x).filter (fun m ↦ d * m < x),
            F (d * m) d := by
      apply Finset.sum_congr rfl
      intro d hd
      let S : Finset ℕ := (gsPositiveBelow x).filter fun n ↦ d ∣ n
      let T : Finset ℕ := (gsPositiveBelow x).filter fun m ↦ d * m < x
      have hdPos : 0 < d := (Finset.mem_Ico.mp hd).1
      change (∑ n ∈ S, F n d) = ∑ m ∈ T, F (d * m) d
      refine Finset.sum_bij' (fun n _ ↦ n / d) (fun m _ ↦ d * m) ?_ ?_ ?_ ?_ ?_
      · intro n hn
        have hn' := Finset.mem_filter.mp hn
        have hnIco := Finset.mem_Ico.mp hn'.1
        have hnDiv := hn'.2
        have hquotPos : 0 < n / d :=
          Nat.div_pos (Nat.le_of_dvd hnIco.1 hnDiv) hdPos
        have hquotLt : n / d < x := (Nat.div_le_self n d).trans_lt hnIco.2
        have hmul : d * (n / d) < x := by
          simpa [Nat.mul_div_cancel' hnDiv] using hnIco.2
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_Ico.mpr ⟨hquotPos, hquotLt⟩, hmul⟩
      · intro m hm
        have hm' := Finset.mem_filter.mp hm
        have hmIco := Finset.mem_Ico.mp hm'.1
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_Ico.mpr ⟨Nat.mul_pos hdPos hmIco.1, hm'.2⟩,
            dvd_mul_right d m⟩
      · intro n hn
        exact Nat.mul_div_cancel' (Finset.mem_filter.mp hn).2
      · intro m hm
        exact Nat.mul_div_cancel_left m hdPos
      · intro n hn
        rw [Nat.mul_div_cancel' (Finset.mem_filter.mp hn).2]

/-- A bounded first factor leaves only the reciprocal mass of the second
factor in a finite Dirichlet-convolution prefix. -/
private theorem norm_positivePrefixSum_mul_le_reciprocalMass
    (a b : ArithmeticFunction ℂ) (X : ℕ)
    (ha : ∀ n, 0 < n → ‖a n‖ ≤ 1) :
    ‖positivePrefixSum (fun n ↦ (a * b) n) X‖ ≤
      (X : ℝ) * ∑ c ∈ Finset.Icc 1 X, ‖b c‖ / (c : ℝ) := by
  classical
  have hprefix : positivePrefixSum (fun n ↦ (a * b) n) X =
      ∑ n ∈ gsPositiveBelow (X + 1), (a * b) n := by
    unfold positivePrefixSum gsPositiveBelow
    rw [Finset.sum_Ico_eq_sub (fun n ↦ (a * b) n) (by omega)]
    simp
  rw [hprefix]
  calc
    ‖∑ n ∈ gsPositiveBelow (X + 1), (a * b) n‖ ≤
        ∑ n ∈ gsPositiveBelow (X + 1), ‖(a * b) n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ gsPositiveBelow (X + 1),
        ∑ c ∈ n.divisors, ‖b c‖ := by
      apply Finset.sum_le_sum
      intro n hn
      rw [show a * b = b * a by exact mul_comm a b,
        ArithmeticFunction.mul_apply,
        Nat.sum_divisorsAntidiagonal (fun c m ↦ b c * a m)]
      refine (norm_sum_le _ _).trans ?_
      apply Finset.sum_le_sum
      intro c hc
      rw [norm_mul]
      have hnpos : 0 < n := (Finset.mem_Ico.mp hn).1
      have hcdiv : c ∣ n := Nat.dvd_of_mem_divisors hc
      have hcpos : 0 < c := Nat.pos_of_dvd_of_pos hcdiv hnpos
      have hquotpos : 0 < n / c := Nat.div_pos
        (Nat.le_of_dvd hnpos hcdiv) hcpos
      exact mul_le_of_le_one_right (norm_nonneg _) (ha _ hquotpos)
    _ = ∑ c ∈ gsPositiveBelow (X + 1),
        ∑ m ∈ (gsPositiveBelow (X + 1)).filter (fun m ↦ c * m < X + 1),
          ‖b c‖ := by
      exact sum_divisors_reindex_real (X + 1) (fun _ c ↦ ‖b c‖)
    _ ≤ (X : ℝ) * ∑ c ∈ Finset.Icc 1 X, ‖b c‖ / (c : ℝ) := by
      have hset : gsPositiveBelow (X + 1) = Finset.Icc 1 X := by
        ext c
        simp [gsPositiveBelow]
      rw [hset]
      calc
        (∑ c ∈ Finset.Icc 1 X,
            ∑ m ∈ (gsPositiveBelow (X + 1)).filter
              (fun m ↦ c * m < X + 1), ‖b c‖) ≤
            ∑ c ∈ Finset.Icc 1 X,
              ((X / c : ℕ) : ℝ) * ‖b c‖ := by
          apply Finset.sum_le_sum
          intro c hc
          have hcpos : 0 < c := (Finset.mem_Icc.mp hc).1
          let S := (gsPositiveBelow (X + 1)).filter
            (fun m ↦ c * m < X + 1)
          have hsub : S ⊆ Finset.Icc 1 (X / c) := by
            intro m hm
            have hm' := Finset.mem_filter.mp hm
            have hmpos : 1 ≤ m := (Finset.mem_Ico.mp hm'.1).1
            have hcm : c * m ≤ X := by omega
            exact Finset.mem_Icc.mpr ⟨hmpos,
              (Nat.le_div_iff_mul_le hcpos).2 (by simpa [mul_comm] using hcm)⟩
          have hcard : S.card ≤ X / c := by
            calc
              S.card ≤ (Finset.Icc 1 (X / c)).card := Finset.card_le_card hsub
              _ ≤ X / c := by simp
          change (∑ _m ∈ S, ‖b c‖) ≤ ((X / c : ℕ) : ℝ) * ‖b c‖
          rw [Finset.sum_const, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (norm_nonneg _)
        _ ≤ ∑ c ∈ Finset.Icc 1 X,
              ((X : ℝ) / (c : ℝ)) * ‖b c‖ := by
          apply Finset.sum_le_sum
          intro c hc
          exact mul_le_mul_of_nonneg_right Nat.cast_div_le (norm_nonneg _)
        _ = (X : ℝ) * ∑ c ∈ Finset.Icc 1 X, ‖b c‖ / (c : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro c hc
          have hc0 : (c : ℝ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hc).1)
          field_simp

theorem gsA10ShiuWeight_le_one
    (y : ℕ) {eta : ℝ} (heta : 0 ≤ eta) (n : ℕ) :
    gsA10ShiuWeight y eta n ≤ 1 := by
  unfold gsA10ShiuWeight
  split
  · exact zero_le_one
  · apply Real.rpow_le_one_of_one_le_of_nonpos
    · exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (primeBandPart_ne_zero (fun p ↦ ¬ p ≤ y) n)
    · exact neg_nonpos.mpr heta

private theorem nat_self_le_two_pow : ∀ k : ℕ, k ≤ 2 ^ k
  | 0 => by simp
  | k + 1 => by
      rw [pow_succ]
      have hk := nat_self_le_two_pow k
      have hp : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      omega

/-- The finite weight obtained by resolving a higher-prime-power index into
its prime and exponent. -/
private def gsA10HigherPrimePowerGeometricWeight
    (y X c : ℕ) : ℝ :=
  ∑ p ∈ (primesUpTo X).filter (fun p ↦ y < p),
    ∑ k ∈ Finset.Icc 2 X,
      if p ^ k = c then
        Real.log p * (((2 : ℝ) ^ k - 1) / (p : ℝ) ^ k)
      else 0

private theorem gsA10HigherPrimePowerGeometricWeight_nonneg
    (y X c : ℕ) : 0 ≤ gsA10HigherPrimePowerGeometricWeight y X c := by
  unfold gsA10HigherPrimePowerGeometricWeight
  apply Finset.sum_nonneg
  intro p hp
  have hpprime := (mem_primesUpTo.mp (Finset.mem_filter.mp hp).1).1
  apply Finset.sum_nonneg
  intro k hk
  split
  · exact mul_nonneg
      (Real.log_nonneg (by exact_mod_cast hpprime.one_lt.le))
      (div_nonneg (sub_nonneg.mpr (one_le_pow₀ (by norm_num)))
        (pow_nonneg (Nat.cast_nonneg _) _))
  · exact le_rfl

private theorem norm_higherPrimePowerPart_div_le_weight
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y X c : ℕ} (hc : c ∈ Finset.Icc 1 X) :
    ‖gsHigherPrimePowerPart (gsA9HighGeneralizedMangoldt hmul y) c‖ /
        (c : ℝ) ≤
      gsA10HigherPrimePowerGeometricWeight y X c := by
  classical
  by_cases hzero :
      gsHigherPrimePowerPart (gsA9HighGeneralizedMangoldt hmul y) c = 0
  · rw [hzero, norm_zero, zero_div]
    exact gsA10HigherPrimePowerGeometricWeight_nonneg y X c
  have hcond : IsPrimePow c ∧ ¬ c.Prime := by
    by_contra h
    apply hzero
    simp [gsHigherPrimePowerPart_apply, h]
  obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff c).mp hcond.1
  have hk2 : 2 ≤ k := by
    have hk1 : k ≠ 1 := by
      intro heq
      subst k
      simp at hpk
      exact hcond.2 (hpk ▸ hp)
    omega
  have hpX : p ≤ X := by
    calc
      p ≤ p ^ k := Nat.le_self_pow hk.ne' p
      _ = c := hpk
      _ ≤ X := (Finset.mem_Icc.mp hc).2
  have hkX : k ≤ X := by
    calc
      k ≤ 2 ^ k := nat_self_le_two_pow k
      _ ≤ p ^ k := Nat.pow_le_pow_left hp.two_le k
      _ = c := hpk
      _ ≤ X := (Finset.mem_Icc.mp hc).2
  have hyp : y < p := by
    by_contra h
    have hpy : p ≤ y := by omega
    have hz := gsA9HighGeneralizedMangoldt_apply_prime_pow_eq_zero
      hmul y hp hpy (k := k)
    apply hzero
    simp [gsHigherPrimePowerPart_apply, hpk.symm, hz]
  have hpmem : p ∈ (primesUpTo X).filter (fun p ↦ y < p) := by
    exact Finset.mem_filter.mpr
      ⟨mem_primesUpTo.mpr ⟨hp, hpX⟩, hyp⟩
  have hkmem : k ∈ Finset.Icc 2 X := Finset.mem_Icc.mpr ⟨hk2, hkX⟩
  have hcposR : (0 : ℝ) < c := by
    exact_mod_cast (show 0 < c from (Finset.mem_Icc.mp hc).1)
  have hboundLambda := norm_gsA9HighGeneralizedMangoldt_prime_pow_le_geometric
    hmul hbound y p k hp
  have hterm :
      ‖gsHigherPrimePowerPart (gsA9HighGeneralizedMangoldt hmul y) c‖ /
          (c : ℝ) ≤
        Real.log p * (((2 : ℝ) ^ k - 1) / (p : ℝ) ^ k) := by
    rw [gsHigherPrimePowerPart_apply, if_pos hcond, ← hpk]
    rw [Nat.cast_pow]
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hpkposR : (0 : ℝ) < (p : ℝ) ^ k := pow_pos hpR _
    apply (div_le_iff₀ hpkposR).2
    calc
      ‖gsA9HighGeneralizedMangoldt hmul y (p ^ k)‖ ≤
          ((2 : ℝ) ^ k - 1) * Real.log p := hboundLambda
      _ = (Real.log p * (((2 : ℝ) ^ k - 1) / (p : ℝ) ^ k)) *
          (p : ℝ) ^ k := by field_simp
  unfold gsA10HigherPrimePowerGeometricWeight
  calc
    _ ≤ ∑ k' ∈ Finset.Icc 2 X,
        if p ^ k' = c then
          Real.log p * (((2 : ℝ) ^ k' - 1) / (p : ℝ) ^ k')
        else 0 := by
      refine hterm.trans ?_
      have hnonneg : ∀ k' ∈ Finset.Icc 2 X,
          0 ≤ if p ^ k' = c then
            Real.log p * (((2 : ℝ) ^ k' - 1) / (p : ℝ) ^ k')
          else 0 := by
        intro k' hk'
        split
        · exact mul_nonneg
            (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))
            (div_nonneg (sub_nonneg.mpr (one_le_pow₀ (by norm_num)))
              (pow_nonneg (Nat.cast_nonneg _) _))
        · exact le_rfl
      simpa [hpk] using Finset.single_le_sum hnonneg hkmem
    _ ≤ ∑ p' ∈ (primesUpTo X).filter (fun p ↦ y < p),
        ∑ k' ∈ Finset.Icc 2 X,
          if p' ^ k' = c then
            Real.log p' * (((2 : ℝ) ^ k' - 1) / (p' : ℝ) ^ k')
          else 0 := by
      have hnonneg : ∀ p' ∈ (primesUpTo X).filter (fun p ↦ y < p),
          0 ≤ ∑ k' ∈ Finset.Icc 2 X,
            if p' ^ k' = c then
              Real.log p' * (((2 : ℝ) ^ k' - 1) / (p' : ℝ) ^ k')
            else 0 := by
        intro p' hp'
        have hpprime := (mem_primesUpTo.mp (Finset.mem_filter.mp hp').1).1
        apply Finset.sum_nonneg
        intro k' hk'
        split
        · exact mul_nonneg
            (Real.log_nonneg (by exact_mod_cast hpprime.one_lt.le))
            (div_nonneg (sub_nonneg.mpr (one_le_pow₀ (by norm_num)))
              (pow_nonneg (Nat.cast_nonneg _) _))
        · exact le_rfl
      exact Finset.single_le_sum hnonneg hpmem

private theorem sum_higherPrimePowerGeometricWeight_le_mass
    (y X : ℕ) :
    (∑ c ∈ Finset.Icc 1 X,
      gsA10HigherPrimePowerGeometricWeight y X c) ≤
        gsA10HigherPrimePowerGeometricMass y X := by
  classical
  unfold gsA10HigherPrimePowerGeometricWeight
  unfold gsA10HigherPrimePowerGeometricMass
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro p hp
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  by_cases hpkX : p ^ k ≤ X
  · have hpkpos : 1 ≤ p ^ k := by
      have hpprime := (mem_primesUpTo.mp (Finset.mem_filter.mp hp).1).1
      exact Nat.one_le_pow _ _ hpprime.pos
    rw [Finset.sum_eq_single (p ^ k)]
    · simp
    · intro c hc hne
      simp [hne.symm]
    · intro hnot
      exact (hnot (Finset.mem_Icc.mpr ⟨hpkpos, hpkX⟩)).elim
  · have hzero : ∀ c ∈ Finset.Icc 1 X,
        (if p ^ k = c then
          Real.log p * (((2 : ℝ) ^ k - 1) / (p : ℝ) ^ k)
        else 0) = 0 := by
      intro c hc
      rw [if_neg]
      intro heq
      exact hpkX (heq.trans_le (Finset.mem_Icc.mp hc).2)
    rw [Finset.sum_eq_zero hzero]
    have hpprime := (mem_primesUpTo.mp (Finset.mem_filter.mp hp).1).1
    exact mul_nonneg
      (Real.log_nonneg (by exact_mod_cast hpprime.one_lt.le))
      (div_nonneg (sub_nonneg.mpr (one_le_pow₀ (by norm_num)))
        (pow_nonneg (Nat.cast_nonneg _) _))

theorem sum_norm_shift_higherPrimePowerPart_div_le_mass
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y X : ℕ} {alpha : ℝ} (halpha : 0 ≤ alpha) :
    (∑ c ∈ Finset.Icc 1 X,
      ‖gsRealShift alpha
        (gsHigherPrimePowerPart (gsA9HighGeneralizedMangoldt hmul y)) c‖ /
          (c : ℝ)) ≤
      gsA10HigherPrimePowerGeometricMass y X := by
  calc
    _ ≤ ∑ c ∈ Finset.Icc 1 X,
        ‖gsHigherPrimePowerPart (gsA9HighGeneralizedMangoldt hmul y) c‖ /
          (c : ℝ) := by
      apply Finset.sum_le_sum
      intro c hc
      have hcpos : 0 < c := (Finset.mem_Icc.mp hc).1
      rw [gsRealShift_apply_of_ne_zero alpha _ hcpos.ne', norm_mul,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.exp_nonneg _)]
      have hlog : 0 ≤ Real.log (c : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ c from hcpos))
      have hexp : Real.exp (-alpha * Real.log (c : ℝ)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr halpha) hlog)
      exact div_le_div_of_nonneg_right
        (mul_le_of_le_one_left (norm_nonneg _) hexp) (Nat.cast_nonneg _)
    _ ≤ ∑ c ∈ Finset.Icc 1 X,
        gsA10HigherPrimePowerGeometricWeight y X c := by
      exact Finset.sum_le_sum fun c hc ↦
        norm_higherPrimePowerPart_div_le_weight hmul hbound hc
    _ ≤ gsA10HigherPrimePowerGeometricMass y X :=
      sum_higherPrimePowerGeometricWeight_le_mass y X

/-- Higher-prime-power component of the second source secondary prefix. -/
def gsA10SecondSecondaryHigherPrimePowerPrefix
    (low high lambda : ArithmeticFunction ℂ)
    (X : ℕ) (eta : ℝ) : ℂ :=
  ∫ alpha in 0..eta,
    positivePrefixSum
      (fun n ↦ ((low * gsRealShift alpha (gsHigherPrimePowerPart lambda)) *
        gsRealShift (2 * eta + alpha) high) n) X

/-- The ordinary-multiplicative higher-prime-power part of the second
secondary is bounded by its geometric mass.  The four-term alternating low
coefficient remains whole throughout the convolution. -/
theorem norm_gsA10TwoBlockSecondSecondaryHigherPrimePowerPrefix_le_mass
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ} {eta : ℝ} (heta : 0 ≤ eta)
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y) :
    ‖gsA10SecondSecondaryHigherPrimePowerPrefix
        (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
        (gsA9HighArithmetic f y)
        (gsA9HighGeneralizedMangoldt hmul y) X eta‖ ≤
      eta * (X : ℝ) * gsA10HigherPrimePowerGeometricMass y X := by
  let low := gsA10TwoBlockAlternatingLow f P₁ P₂ y
  let high := gsA9HighArithmetic f y
  let lambda := gsA9HighGeneralizedMangoldt hmul y
  unfold gsA10SecondSecondaryHigherPrimePowerPrefix
  rw [show eta * (X : ℝ) * gsA10HigherPrimePowerGeometricMass y X =
      eta * ((X : ℝ) * gsA10HigherPrimePowerGeometricMass y X) by ring]
  apply norm_intervalIntegral_positivePrefixSum_le heta
  intro alpha halpha
  let gamma : ℝ := 2 * eta + alpha
  let a : ArithmeticFunction ℂ := low * gsRealShift gamma high
  let b : ArithmeticFunction ℂ :=
    gsRealShift alpha (gsHigherPrimePowerPart lambda)
  have hgamma : 0 ≤ gamma := by
    dsimp [gamma]
    linarith [halpha.1]
  have ha : ∀ n, 0 < n → ‖a n‖ ≤ 1 := by
    intro n hn
    dsimp [a, low, high]
    exact (norm_gsA10FirstSecondaryCoefficient_le_shiuWeight
      hmul hbound P₁ P₂ y hQ₂ hQ₃ gamma hn).trans
        (gsA10ShiuWeight_le_one y hgamma n)
  have hreassoc :
      (low * gsRealShift alpha (gsHigherPrimePowerPart lambda)) *
          gsRealShift gamma high = a * b := by
    dsimp [a, b]
    ring
  change ‖positivePrefixSum
      (fun n ↦ ((low * gsRealShift alpha (gsHigherPrimePowerPart lambda)) *
        gsRealShift gamma high) n) X‖ ≤
      (X : ℝ) * gsA10HigherPrimePowerGeometricMass y X
  rw [hreassoc]
  exact (norm_positivePrefixSum_mul_le_reciprocalMass a b X ha).trans
    (mul_le_mul_of_nonneg_left
      (sum_norm_shift_higherPrimePowerPart_div_le_mass
        hmul hbound halpha.1) (Nat.cast_nonneg _))

/-- Closed higher-prime-power error at a shift of length at most one. -/
theorem norm_gsA10TwoBlockSecondSecondaryHigherPrimePowerPrefix_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ} (hy : 3 ≤ y) (hyX : y ≤ X)
    {eta : ℝ} (heta : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y) :
    ‖gsA10SecondSecondaryHigherPrimePowerPrefix
        (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
        (gsA9HighArithmetic f y)
        (gsA9HighGeneralizedMangoldt hmul y) X eta‖ ≤
      12 * (X : ℝ) * Real.log X / y *
        PrimeEstimates.primeReciprocals X := by
  have hraw :=
    norm_gsA10TwoBlockSecondSecondaryHigherPrimePowerPrefix_le_mass
      hmul hbound P₁ P₂ (y := y) (X := X) (eta := eta) heta hQ₂ hQ₃
  have hmass := gsA10HigherPrimePowerGeometricMass_le (X := X) hy
  have hlogX : 0 ≤ Real.log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  have hprime : 0 ≤ PrimeEstimates.primeReciprocals X :=
    PrimeEstimates.primeReciprocals_nonneg X
  let E : ℝ := 12 * Real.log X / y * PrimeEstimates.primeReciprocals X
  have hE : 0 ≤ E := by
    dsimp [E]
    positivity
  calc
    _ ≤ eta * (X : ℝ) * gsA10HigherPrimePowerGeometricMass y X := hraw
    _ ≤ eta * (X : ℝ) * E :=
      mul_le_mul_of_nonneg_left hmass
        (mul_nonneg heta (Nat.cast_nonneg _))
    _ ≤ (X : ℝ) * E := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_left (Nat.cast_nonneg _) heta1) hE
    _ = 12 * (X : ℝ) * Real.log X / y *
        PrimeEstimates.primeReciprocals X := by
      dsimp [E]
      ring

end

end Erdos67.MRHalaszBands

#print axioms Erdos67.MRHalaszBands.norm_gsA10TwoBlockSecondSecondaryHigherPrimePowerPrefix_le_mass
#print axioms Erdos67.MRHalaszBands.norm_gsA10TwoBlockSecondSecondaryHigherPrimePowerPrefix_le
