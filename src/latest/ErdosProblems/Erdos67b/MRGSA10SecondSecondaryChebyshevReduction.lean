import ErdosProblems.Erdos67b.MRGSA10WeightedChebyshev
import ErdosProblems.Erdos67b.MRGSA10AlternatingLowNorm
import ErdosProblems.Erdos67b.MRGSA10HighGeneralizedMangoldt
import ErdosProblems.Erdos67b.MRGSA10PrefixIntegralMajorant

/-!
# Chebyshev reduction of the second GS A.10 secondary

The distinguished generalized-Mangoldt variable is summed before either
of the other two convolution variables.  This preserves the cutoff
`k ≤ X / (mn)` and hence the factor `X^(1-alpha)` used in source Lemma 2.4.
-/

open scoped BigOperators

namespace Erdos67b.MRHalaszBands

noncomputable section

/-- A finite positive Dirichlet mass. -/
def gsFiniteNormDirichletMass
    (a : ArithmeticFunction ℂ) (X : ℕ) (sigma : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 X, ‖a n‖ * (n : ℝ) ^ (-sigma)

def gsPositiveBelow (x : ℕ) : Finset ℕ := Finset.Ico 1 x

theorem divisors_eq_gsPositiveBelow_filter_dvd {x n : ℕ}
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

theorem sum_divisors_reindex {R : Type*} [AddCommMonoid R]
    (x : ℕ) (F : ℕ → ℕ → R) :
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
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_Ico.mpr
            ⟨hquotPos, (Nat.div_le_self n d).trans_lt hnIco.2⟩,
            by simpa [Nat.mul_div_cancel' hnDiv] using hnIco.2⟩
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

theorem sum_divisors_reindex_real
    (x : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ n ∈ gsPositiveBelow x, ∑ d ∈ n.divisors, F n d) =
      ∑ d ∈ gsPositiveBelow x,
        ∑ m ∈ (gsPositiveBelow x).filter (fun m ↦ d * m < x),
          F (d * m) d :=
  sum_divisors_reindex x F

/-- Reindex a finite convolution prefix so the second factor retains its
natural cutoff. -/
theorem norm_positivePrefixSum_mul_le_cutoff
    (a b : ArithmeticFunction ℂ) (X : ℕ) :
    ‖positivePrefixSum (fun n ↦ (a * b) n) X‖ ≤
      ∑ d ∈ Finset.Icc 1 X, ‖a d‖ *
        (∑ m ∈ Finset.Icc 1 (X / d), ‖b m‖) := by
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
        ∑ d ∈ n.divisors, ‖a d‖ * ‖b (n / d)‖ := by
      apply Finset.sum_le_sum
      intro n hn
      rw [ArithmeticFunction.mul_apply,
        Nat.sum_divisorsAntidiagonal (fun d m ↦ a d * b m)]
      refine (norm_sum_le _ _).trans ?_
      apply Finset.sum_le_sum
      intro d hd
      rw [norm_mul]
    _ = ∑ d ∈ gsPositiveBelow (X + 1),
        ∑ m ∈ (gsPositiveBelow (X + 1)).filter (fun m ↦ d * m < X + 1),
          ‖a d‖ * ‖b m‖ := by
      rw [sum_divisors_reindex_real (X + 1)
        (fun n d ↦ ‖a d‖ * ‖b (n / d)‖)]
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro m hm
      rw [Nat.mul_div_cancel_left m (Finset.mem_Ico.mp hd).1]
    _ ≤ ∑ d ∈ Finset.Icc 1 X, ‖a d‖ *
        (∑ m ∈ Finset.Icc 1 (X / d), ‖b m‖) := by
      have hset : gsPositiveBelow (X + 1) = Finset.Icc 1 X := by
        ext d
        simp [gsPositiveBelow]
      rw [hset]
      apply Finset.sum_le_sum
      intro d hd
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro m hm
        have hm' := Finset.mem_filter.mp hm
        have hmpos : 1 ≤ m := (Finset.mem_Ico.mp hm'.1).1
        have hdm : d * m ≤ X := by omega
        exact Finset.mem_Icc.mpr ⟨hmpos,
          (Nat.le_div_iff_mul_le (Finset.mem_Icc.mp hd).1).2
            (by simpa [mul_comm] using hdm)⟩
      · intro m _ _
        positivity

/-- A finite weighted convolution mass is bounded by the product of the
two finite weighted masses. -/
theorem gsFiniteNormDirichletMass_mul_le
    (a b : ArithmeticFunction ℂ) (X : ℕ) {sigma : ℝ}
    (hsigma : 0 ≤ sigma) :
    gsFiniteNormDirichletMass (a * b) X sigma ≤
      gsFiniteNormDirichletMass a X sigma *
        gsFiniteNormDirichletMass b X sigma := by
  classical
  unfold gsFiniteNormDirichletMass
  calc
    (∑ n ∈ Finset.Icc 1 X, ‖(a * b) n‖ * (n : ℝ) ^ (-sigma)) ≤
        ∑ n ∈ Finset.Icc 1 X,
          (∑ d ∈ n.divisors, ‖a d‖ * ‖b (n / d)‖) *
            (n : ℝ) ^ (-sigma) := by
      apply Finset.sum_le_sum
      intro n hn
      apply mul_le_mul_of_nonneg_right
      · rw [ArithmeticFunction.mul_apply,
          Nat.sum_divisorsAntidiagonal (fun d m ↦ a d * b m)]
        exact (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun d hd ↦ by rw [norm_mul])
      · positivity
    _ = ∑ n ∈ gsPositiveBelow (X + 1),
          ∑ d ∈ n.divisors,
            (‖a d‖ * (d : ℝ) ^ (-sigma)) *
              (‖b (n / d)‖ * ((n / d : ℕ) : ℝ) ^ (-sigma)) := by
      have hset : Finset.Icc 1 X = gsPositiveBelow (X + 1) := by
        ext n
        simp [gsPositiveBelow]
      rw [hset]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d hd
      have hnpos : 0 < n := (Finset.mem_Ico.mp hn).1
      have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hnpos
      have hqpos : 0 < n / d := Nat.div_pos
        (Nat.le_of_dvd hnpos hdvd) hdpos
      have hnEq : d * (n / d) = n := Nat.mul_div_cancel' hdvd
      have hcast : (n : ℝ) = (d : ℝ) * ((n / d : ℕ) : ℝ) := by
        exact_mod_cast hnEq.symm
      rw [hcast, Real.mul_rpow (by positivity) (by positivity)]
      ring
    _ = ∑ d ∈ gsPositiveBelow (X + 1),
        ∑ m ∈ (gsPositiveBelow (X + 1)).filter (fun m ↦ d * m < X + 1),
          (‖a d‖ * (d : ℝ) ^ (-sigma)) *
            (‖b m‖ * (m : ℝ) ^ (-sigma)) := by
      rw [sum_divisors_reindex_real (X + 1)
        (fun n d ↦ (‖a d‖ * (d : ℝ) ^ (-sigma)) *
          (‖b (n / d)‖ * ((n / d : ℕ) : ℝ) ^ (-sigma)))]
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro m hm
      rw [Nat.mul_div_cancel_left m (Finset.mem_Ico.mp hd).1]
    _ ≤ (∑ d ∈ Finset.Icc 1 X, ‖a d‖ * (d : ℝ) ^ (-sigma)) *
        (∑ m ∈ Finset.Icc 1 X, ‖b m‖ * (m : ℝ) ^ (-sigma)) := by
      have hset : gsPositiveBelow (X + 1) = Finset.Icc 1 X := by
        ext n
        simp [gsPositiveBelow]
      rw [hset, Finset.sum_mul]
      apply Finset.sum_le_sum
      intro d hd
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro m _ _
        positivity

/-- The alternating low coefficient is globally one-bounded: off its
low-prime support it vanishes. -/
theorem norm_gsA10TwoBlockAlternatingLow_le_one
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (y : ℕ)
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y) :
    ∀ n, 0 < n → ‖gsA10TwoBlockAlternatingLow f P₁ P₂ y n‖ ≤ 1 := by
  intro n hn
  by_cases hsupp : PrimeSupported (fun p ↦ p ≤ y) n
  · exact norm_gsA10TwoBlockAlternatingLow_le_one_of_lowSupported
      hmul hbound P₁ P₂ y hn hQ₂ hQ₃ hsupp
  · rw [gsA10TwoBlockAlternatingLow_eq_zero_of_not_lowSupported
      f P₁ P₂ y hn.ne' hsupp, norm_zero]
    norm_num

/-- The distinguished high generalized-Mangoldt shift has the weighted
Chebyshev prefix bound. -/
theorem sum_norm_gsRealShift_highGeneralizedMangoldt_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (y K : ℕ) {alpha : ℝ} (halpha0 : 0 ≤ alpha)
    (halphaHalf : alpha ≤ 1 / 2) :
    (∑ k ∈ Finset.Icc 1 K,
      ‖gsRealShift alpha (gsA9HighGeneralizedMangoldt hmul y) k‖) ≤
      12 * (Real.log 4 + 4) * (K : ℝ) ^ (1 - alpha) := by
  by_cases hK : 2 ≤ K
  · calc
      (∑ k ∈ Finset.Icc 1 K,
          ‖gsRealShift alpha (gsA9HighGeneralizedMangoldt hmul y) k‖) ≤
          ∑ k ∈ Finset.Icc 1 K,
            ArithmeticFunction.vonMangoldt k * (k : ℝ) ^ (-alpha) := by
        apply Finset.sum_le_sum
        intro k hk
        have hkpos : 0 < k := (Finset.mem_Icc.mp hk).1
        rw [gsRealShift_apply_of_ne_zero alpha _ hkpos.ne', norm_mul,
          Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.exp_nonneg _)]
        have hexp : Real.exp (-alpha * Real.log (k : ℝ)) =
            (k : ℝ) ^ (-alpha) := by
          rw [Real.rpow_def_of_pos (by exact_mod_cast hkpos)]
          congr 1
          ring
        rw [hexp]
        simpa [mul_comm] using mul_le_mul_of_nonneg_right
          (norm_gsA9HighGeneralizedMangoldt_le_vonMangoldt
            hmul hcomp hbound y k)
          (Real.rpow_nonneg (by positivity) (-alpha))
      _ ≤ _ := sum_vonMangoldt_mul_rpow_neg_le hK halpha0 halphaHalf
  · have hKle : K ≤ 1 := by omega
    have hset : Finset.Icc 1 K ⊆ {1} := by
      intro k hk
      simp only [Finset.mem_Icc, Finset.mem_singleton] at hk ⊢
      omega
    have hzero : ∀ k ∈ Finset.Icc 1 K,
        ‖gsRealShift alpha (gsA9HighGeneralizedMangoldt hmul y) k‖ = 0 := by
      intro k hk
      have hk1 : k = 1 := Finset.mem_singleton.mp (hset hk)
      subst k
      simp [gsRealShift, gsA9HighGeneralizedMangoldt,
        gsGeneralizedMangoldt_one]
    rw [Finset.sum_eq_zero hzero]
    positivity

private theorem cast_div_rpow_le_mul_rpow_neg
    {X d : ℕ} (hd : 0 < d) {sigma : ℝ} (hsigma : 0 ≤ sigma) :
    ((X / d : ℕ) : ℝ) ^ sigma ≤
      (X : ℝ) ^ sigma * (d : ℝ) ^ (-sigma) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hcast : ((X / d : ℕ) : ℝ) ≤ (X : ℝ) / (d : ℝ) :=
    Nat.cast_div_le
  calc
    ((X / d : ℕ) : ℝ) ^ sigma ≤
        ((X : ℝ) / (d : ℝ)) ^ sigma :=
      Real.rpow_le_rpow (by positivity) hcast hsigma
    _ = (X : ℝ) ^ sigma / (d : ℝ) ^ sigma := by
      rw [Real.div_rpow (Nat.cast_nonneg X) hdR.le]
    _ = (X : ℝ) ^ sigma * (d : ℝ) ^ (-sigma) := by
      rw [Real.rpow_neg hdR.le]
      ring

/-- A real shift simply adds its exponent to a finite norm-Dirichlet mass. -/
theorem gsFiniteNormDirichletMass_gsRealShift
    (a : ArithmeticFunction ℂ) (X : ℕ) (rho sigma : ℝ) :
    gsFiniteNormDirichletMass (gsRealShift rho a) X sigma =
      gsFiniteNormDirichletMass a X (sigma + rho) := by
  unfold gsFiniteNormDirichletMass
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
  rw [gsRealShift_apply_of_ne_zero rho a hnpos.ne', norm_mul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_nonneg _)]
  have hexp : Real.exp (-rho * Real.log (n : ℝ)) =
      (n : ℝ) ^ (-rho) := by
    rw [Real.rpow_def_of_pos (by exact_mod_cast hnpos)]
    congr 1
    ring
  rw [hexp]
  calc
    (n : ℝ) ^ (-rho) * ‖a n‖ * (n : ℝ) ^ (-sigma) =
        ‖a n‖ * ((n : ℝ) ^ (-rho) * (n : ℝ) ^ (-sigma)) := by ring
    _ = ‖a n‖ * (n : ℝ) ^ (-rho + -sigma) := by
      rw [Real.rpow_add (by positivity)]
    _ = ‖a n‖ * (n : ℝ) ^ (-(sigma + rho)) := by
      congr 2
      ring

/-- Pointwise source Lemma 2.4 estimate after summing the distinguished
generalized-Mangoldt variable first.  The two remaining finite Euler masses
are kept explicit, and the exponent of the high mass is already independent
of `alpha`. -/
theorem norm_positivePrefixSum_secondSecondaryIntegrand_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ}
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y)
    {eta alpha : ℝ} (halpha0 : 0 ≤ alpha)
    (halphaHalf : alpha ≤ 1 / 2) (halphaOne : alpha ≤ 1) :
    ‖positivePrefixSum
        (fun n ↦ ((gsA10TwoBlockAlternatingLow f P₁ P₂ y *
            gsRealShift alpha (gsA9HighGeneralizedMangoldt hmul y)) *
          gsRealShift (2 * eta + alpha) (gsA9HighArithmetic f y)) n) X‖ ≤
      12 * (Real.log 4 + 4) * (X : ℝ) ^ (1 - alpha) *
        gsFiniteNormDirichletMass
          (gsA10TwoBlockAlternatingLow f P₁ P₂ y) X (1 - alpha) *
        gsFiniteNormDirichletMass
          (gsA9HighArithmetic f y) X (1 + 2 * eta) := by
  let low := gsA10TwoBlockAlternatingLow f P₁ P₂ y
  let lambda := gsA9HighGeneralizedMangoldt hmul y
  let high := gsA9HighArithmetic f y
  let lambdaShift := gsRealShift alpha lambda
  let highShift := gsRealShift (2 * eta + alpha) high
  let C : ℝ := 12 * (Real.log 4 + 4)
  have hreorder : (low * lambdaShift) * highShift =
      (low * highShift) * lambdaShift := by ring
  rw [show (fun n ↦ ((low * lambdaShift) * highShift) n) =
      (fun n ↦ ((low * highShift) * lambdaShift) n) by rw [hreorder]]
  have hcut := norm_positivePrefixSum_mul_le_cutoff
    (low * highShift) lambdaShift X
  refine hcut.trans ?_
  calc
    (∑ d ∈ Finset.Icc 1 X, ‖(low * highShift) d‖ *
        ∑ k ∈ Finset.Icc 1 (X / d), ‖lambdaShift k‖) ≤
        ∑ d ∈ Finset.Icc 1 X, ‖(low * highShift) d‖ *
          (C * ((X / d : ℕ) : ℝ) ^ (1 - alpha)) := by
      apply Finset.sum_le_sum
      intro d hd
      apply mul_le_mul_of_nonneg_left
      · exact sum_norm_gsRealShift_highGeneralizedMangoldt_le
          hmul hcomp hbound y (X / d) halpha0 halphaHalf
      · exact norm_nonneg _
    _ ≤ ∑ d ∈ Finset.Icc 1 X, ‖(low * highShift) d‖ *
          (C * ((X : ℝ) ^ (1 - alpha) *
            (d : ℝ) ^ (-(1 - alpha)))) := by
      apply Finset.sum_le_sum
      intro d hd
      apply mul_le_mul_of_nonneg_left
      apply mul_le_mul_of_nonneg_left
      · exact cast_div_rpow_le_mul_rpow_neg
          (Finset.mem_Icc.mp hd).1 (by linarith)
      · positivity
      · exact norm_nonneg _
    _ = C * (X : ℝ) ^ (1 - alpha) *
        gsFiniteNormDirichletMass (low * highShift) X (1 - alpha) := by
      unfold gsFiniteNormDirichletMass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ C * (X : ℝ) ^ (1 - alpha) *
        (gsFiniteNormDirichletMass low X (1 - alpha) *
          gsFiniteNormDirichletMass highShift X (1 - alpha)) := by
      apply mul_le_mul_of_nonneg_left
      · exact gsFiniteNormDirichletMass_mul_le low highShift X
          (by linarith)
      · positivity
    _ = C * (X : ℝ) ^ (1 - alpha) *
        gsFiniteNormDirichletMass low X (1 - alpha) *
          gsFiniteNormDirichletMass high X (1 + 2 * eta) := by
      rw [gsFiniteNormDirichletMass_gsRealShift]
      rw [show 1 - alpha + (2 * eta + alpha) = 1 + 2 * eta by ring]
      ring

end

end Erdos67b.MRHalaszBands

#print axioms Erdos67b.MRHalaszBands.norm_positivePrefixSum_mul_le_cutoff
#print axioms Erdos67b.MRHalaszBands.gsFiniteNormDirichletMass_mul_le
#print axioms Erdos67b.MRHalaszBands.sum_norm_gsRealShift_highGeneralizedMangoldt_le
#print axioms Erdos67b.MRHalaszBands.norm_positivePrefixSum_secondSecondaryIntegrand_le
