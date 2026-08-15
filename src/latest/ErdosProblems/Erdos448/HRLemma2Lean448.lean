import Mathlib
import ErdosProblems.Erdos448.HalberstamComplete448

/-!
Finite local-factor algebra for Lemma 2 of Erdős--Tenenbaum (1981).

The analytic mean-value engine is deliberately exposed as `hengine` in the
last theorem.  That hypothesis is exactly the output obtained by applying the
Halberstam--Richert Lemma 1 engine to the shifted multiplicative weight.  All
remaining work here--positivity of the local factors, legitimacy of the
quotient defining `w(p^i)`, and replacement of the shifted Euler factors by
the paper's correction factors--is proved without an analytic assumption.

The series are truncated at an arbitrary exponent `J`; this is the form used
for a finite sum over `n <= N`.  Passing to the infinite series is then a
monotone-convergence step, independent of the algebra formalized here.
-/

open scoped BigOperators
open Finset

namespace ErdosTenenbaumLemma2Scratch

/-- The diagonal local Euler factor, truncated after exponent `J`. -/
noncomputable def diagonalLocal
    (u v : ArithmeticFunction ℝ) (p J : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (J + 1),
    u (p ^ j) * v (p ^ j) / ((p ^ j : ℕ) : ℝ)

/-- The local factor at a prime whose exponent in the fixed shift is `i`. -/
noncomputable def shiftedLocal
    (u v : ArithmeticFunction ℝ) (p i J : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (J + 1),
    u (p ^ (i + j)) * v (p ^ j) / ((p ^ j : ℕ) : ℝ)

/-- The numerator in the correction factor `w(p^i)` from Lemma 2. -/
noncomputable def weightedShiftedLocal
    (u v : ArithmeticFunction ℝ) (p i J : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (J + 1),
    u (p ^ (i + j)) * v (p ^ j) *
      (1 + (j : ℝ) * Real.log (p : ℝ)) /
      ((p ^ j : ℕ) : ℝ)

/-- The finite correction factor.  Its denominator is positive under the
standard normalization and nonnegativity assumptions; see
`diagonalLocal_pos`. -/
noncomputable def localCorrection
    (u v : ArithmeticFunction ℝ) (p i J : ℕ) : ℝ :=
  weightedShiftedLocal u v p i J / diagonalLocal u v p J

/-- The shifted convolution sum to which Lemma 2 is applied. -/
noncomputable def shiftedConvolutionSum
    (u v : ArithmeticFunction ℝ) (k N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, u (k * n) * v n

/-- The Euler product furnished by the basic mean-value engine before the
local factors at primes dividing `k` are replaced by `w(p^i)`. -/
noncomputable def basicShiftedEulerProduct
    (u v : ArithmeticFunction ℝ) (k N J : ℕ) : ℝ :=
  ∏ p ∈ (N + 1).primesBelow,
    if p ∈ k.primeFactors then
      shiftedLocal u v p (k.factorization p) J
    else
      diagonalLocal u v p J

/-- The product appearing after the finite local-factor replacement. -/
noncomputable def correctedEulerProduct
    (u v : ArithmeticFunction ℝ) (k N J : ℕ) : ℝ :=
  (∏ p ∈ k.primeFactors ∩ (N + 1).primesBelow,
      localCorrection u v p (k.factorization p) J) *
    ∏ p ∈ (N + 1).primesBelow, diagonalLocal u v p J

/-- The factors of the fixed shift supported on primes beyond the range of
the mean-value Euler product. -/
noncomputable def largePrimeShiftProduct
    (u : ArithmeticFunction ℝ) (k N : ℕ) : ℝ :=
  ∏ p ∈ k.primeFactors \ (N + 1).primesBelow,
    u (p ^ (k.factorization p))

lemma diagonalLocal_nonneg
    (u v : ArithmeticFunction ℝ)
    (hu : ∀ n, 0 ≤ u n) (hv : ∀ n, 0 ≤ v n)
    (p J : ℕ) :
    0 ≤ diagonalLocal u v p J := by
  unfold diagonalLocal
  exact Finset.sum_nonneg fun j hj =>
    div_nonneg (mul_nonneg (hu _) (hv _)) (Nat.cast_nonneg _)

lemma diagonalLocal_pos
    (u v : ArithmeticFunction ℝ)
    (hu_one : u 1 = 1) (hv_one : v 1 = 1)
    (hu : ∀ n, 0 ≤ u n) (hv : ∀ n, 0 ≤ v n)
    (p J : ℕ) :
    0 < diagonalLocal u v p J := by
  have hzero_mem : 0 ∈ Finset.range (J + 1) := by simp
  have hterm_zero :
      u (p ^ 0) * v (p ^ 0) / (((p ^ 0 : ℕ) : ℝ)) = 1 := by
    simp [hu_one, hv_one]
  have hrest :
      0 ≤ ∑ j ∈ (Finset.range (J + 1)).erase 0,
        u (p ^ j) * v (p ^ j) / ((p ^ j : ℕ) : ℝ) := by
    exact Finset.sum_nonneg fun j hj =>
      div_nonneg (mul_nonneg (hu _) (hv _)) (Nat.cast_nonneg _)
  rw [diagonalLocal, ← Finset.add_sum_erase _ _ hzero_mem, hterm_zero]
  linarith

lemma shiftedLocal_nonneg
    (u v : ArithmeticFunction ℝ)
    (hu : ∀ n, 0 ≤ u n) (hv : ∀ n, 0 ≤ v n)
    (p i J : ℕ) :
    0 ≤ shiftedLocal u v p i J := by
  unfold shiftedLocal
  exact Finset.sum_nonneg fun j hj =>
    div_nonneg (mul_nonneg (hu _) (hv _)) (Nat.cast_nonneg _)

lemma weightedShiftedLocal_nonneg
    (u v : ArithmeticFunction ℝ)
    (hu : ∀ n, 0 ≤ u n) (hv : ∀ n, 0 ≤ v n)
    {p : ℕ} (hp : p.Prime) (i J : ℕ) :
    0 ≤ weightedShiftedLocal u v p i J := by
  unfold weightedShiftedLocal
  refine Finset.sum_nonneg fun j hj => div_nonneg ?_ (Nat.cast_nonneg _)
  have hlog : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  exact mul_nonneg (mul_nonneg (hu _) (hv _)) (by positivity)

lemma shiftedLocal_le_weightedShiftedLocal
    (u v : ArithmeticFunction ℝ)
    (hu : ∀ n, 0 ≤ u n) (hv : ∀ n, 0 ≤ v n)
    {p : ℕ} (hp : p.Prime) (i J : ℕ) :
    shiftedLocal u v p i J ≤ weightedShiftedLocal u v p i J := by
  unfold shiftedLocal weightedShiftedLocal
  refine Finset.sum_le_sum fun j hj => ?_
  have hp_cast_pos : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hpow_pos : 0 < p ^ j := pow_pos hp.pos j
  have hdenom_pos : 0 < (((p ^ j : ℕ) : ℝ)) := by exact_mod_cast hpow_pos
  have hbase : 0 ≤ u (p ^ (i + j)) * v (p ^ j) :=
    mul_nonneg (hu _) (hv _)
  have hlog : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  apply (div_le_div_iff_of_pos_right hdenom_pos).2
  nlinarith [mul_nonneg (Nat.cast_nonneg j) hlog]

lemma shiftedLocal_le_correction_mul_diagonal
    (u v : ArithmeticFunction ℝ)
    (hu_one : u 1 = 1) (hv_one : v 1 = 1)
    (hu : ∀ n, 0 ≤ u n) (hv : ∀ n, 0 ≤ v n)
    {p : ℕ} (hp : p.Prime) (i J : ℕ) :
    shiftedLocal u v p i J ≤
      localCorrection u v p i J * diagonalLocal u v p J := by
  have hdiag : diagonalLocal u v p J ≠ 0 :=
    ne_of_gt (diagonalLocal_pos u v hu_one hv_one hu hv p J)
  rw [localCorrection, div_mul_cancel₀ _ hdiag]
  exact shiftedLocal_le_weightedShiftedLocal u v hu hv hp i J

lemma localCorrection_nonneg
    (u v : ArithmeticFunction ℝ)
    (hu_one : u 1 = 1) (hv_one : v 1 = 1)
    (hu : ∀ n, 0 ≤ u n) (hv : ∀ n, 0 ≤ v n)
    {p : ℕ} (hp : p.Prime) (i J : ℕ) :
    0 ≤ localCorrection u v p i J := by
  exact div_nonneg
    (weightedShiftedLocal_nonneg u v hu hv hp i J)
    (diagonalLocal_pos u v hu_one hv_one hu hv p J).le

/-- A reusable finite-product replacement lemma.  It is the algebraic heart
of the passage from the raw shifted Euler product to the correction factors
`w(p^i)` in Erdős--Tenenbaum Lemma 2. -/
lemma product_replace_on_subset
    {S T : Finset ℕ} (hTS : T ⊆ S)
    (A D W : ℕ → ℝ)
    (hD : ∀ p ∈ S, 0 ≤ D p)
    (hA : ∀ p ∈ T, 0 ≤ A p)
    (hW : ∀ p ∈ T, 0 ≤ W p)
    (hADW : ∀ p ∈ T, A p ≤ W p * D p) :
    (∏ p ∈ S, if p ∈ T then A p else D p) ≤
      (∏ p ∈ T, W p) * ∏ p ∈ S, D p := by
  classical
  let B : ℕ → ℝ := fun p => if p ∈ T then W p * D p else D p
  have hpoint : ∀ p ∈ S,
      (if p ∈ T then A p else D p) ≤ B p := by
    intro p hp
    by_cases hpT : p ∈ T
    · simpa [B, hpT] using hADW p hpT
    · simp [B, hpT]
  have hleft_nonneg : ∀ p ∈ S,
      0 ≤ (if p ∈ T then A p else D p) := by
    intro p hp
    by_cases hpT : p ∈ T
    · rw [if_pos hpT]
      exact hA p hpT
    · rw [if_neg hpT]
      exact hD p hp
  have hprod_le :
      (∏ p ∈ S, if p ∈ T then A p else D p) ≤
        ∏ p ∈ S, B p := by
    exact Finset.prod_le_prod hleft_nonneg hpoint
  have hfilter : S.filter (fun p => p ∈ T) = T := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · exact fun hp => hp.2
    · exact fun hp => ⟨hTS hp, hp⟩
  have hBprod :
      (∏ p ∈ S, B p) =
        (∏ p ∈ T, W p) * ∏ p ∈ S, D p := by
    calc
      (∏ p ∈ S, B p) =
          (∏ p ∈ S, (if p ∈ T then W p else 1) * D p) := by
            apply Finset.prod_congr rfl
            intro p hp
            by_cases hpT : p ∈ T <;> simp [B, hpT]
      _ = (∏ p ∈ S, if p ∈ T then W p else 1) *
          ∏ p ∈ S, D p := by rw [Finset.prod_mul_distrib]
      _ = (∏ p ∈ S.filter (fun p => p ∈ T), W p) *
          ∏ p ∈ S, D p := by
            congr 1
            exact (Finset.prod_filter (s := S) (p := fun p => p ∈ T) W).symm
      _ = (∏ p ∈ T, W p) * ∏ p ∈ S, D p := by rw [hfilter]
  exact hprod_le.trans_eq hBprod

lemma basicShiftedEulerProduct_le_correctedEulerProduct
    (u v : ArithmeticFunction ℝ)
    (hu_one : u 1 = 1) (hv_one : v 1 = 1)
    (hu : ∀ n, 0 ≤ u n) (hv : ∀ n, 0 ≤ v n)
    (k N J : ℕ) :
    basicShiftedEulerProduct u v k N J ≤
      correctedEulerProduct u v k N J := by
  classical
  let S := (N + 1).primesBelow
  let T := k.primeFactors ∩ S
  have hTS : T ⊆ S := Finset.inter_subset_right
  have hprime : ∀ p ∈ S, p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primesBelow hp
  have hreplace := product_replace_on_subset hTS
    (fun p => shiftedLocal u v p (k.factorization p) J)
    (fun p => diagonalLocal u v p J)
    (fun p => localCorrection u v p (k.factorization p) J)
    (fun p hp => diagonalLocal_nonneg u v hu hv p J)
    (fun p hp => shiftedLocal_nonneg u v hu hv p (k.factorization p) J)
    (fun p hp => localCorrection_nonneg u v hu_one hv_one hu hv
      (hprime p (hTS hp)) (k.factorization p) J)
    (fun p hp => shiftedLocal_le_correction_mul_diagonal
      u v hu_one hv_one hu hv (hprime p (hTS hp)) (k.factorization p) J)
  have hleft : basicShiftedEulerProduct u v k N J =
      ∏ p ∈ S,
        if p ∈ T then shiftedLocal u v p (k.factorization p) J
        else diagonalLocal u v p J := by
    unfold basicShiftedEulerProduct
    dsimp [S]
    apply Finset.prod_congr rfl
    intro p hp
    have hpS : p ∈ S := by simpa [S] using hp
    simp only [T, Finset.mem_inter, hpS, and_true]
  rw [hleft]
  simpa [correctedEulerProduct, S, T] using hreplace

lemma largePrimeShiftProduct_nonneg
    (u : ArithmeticFunction ℝ) (hu : ∀ n, 0 ≤ u n)
    (k N : ℕ) :
    0 ≤ largePrimeShiftProduct u k N := by
  unfold largePrimeShiftProduct
  exact Finset.prod_nonneg fun p hp => hu _

/-- Finite, consumer-shaped Erdős--Tenenbaum Lemma 2.

`hengine` is precisely the raw mean-value bound supplied by Lemma 1, before
its shifted local Euler factors are divided by the diagonal factors.  The
conclusion contains exactly the correction-product times the common diagonal
Euler product, together with the unchanged large-prime part of the shift.
-/
theorem multiplicative_convolution_mean_value_II_of_basic_engine
    (u v : ArithmeticFunction ℝ)
    (hu_one : u 1 = 1) (hv_one : v 1 = 1)
    (hu : ∀ n, 0 ≤ u n) (hv : ∀ n, 0 ≤ v n)
    (k N J : ℕ) (scale : ℝ) (hscale : 0 ≤ scale)
    (hengine : shiftedConvolutionSum u v k N ≤
      scale * basicShiftedEulerProduct u v k N J *
        largePrimeShiftProduct u k N) :
    shiftedConvolutionSum u v k N ≤
      scale * correctedEulerProduct u v k N J *
        largePrimeShiftProduct u k N := by
  have heuler := basicShiftedEulerProduct_le_correctedEulerProduct
    u v hu_one hv_one hu hv k N J
  have htail := largePrimeShiftProduct_nonneg u hu k N
  exact hengine.trans <|
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left heuler hscale) htail

/-! ## Infinite local factors

These definitions match the displayed statement of Erdős--Tenenbaum Lemma 2
literally.  The following results take summability as an argument.  In the
paper it follows immediately from the prime-power majorant with ratio
`lambda / p < 1`; separating that estimate makes these local-algebra lemmas
usable with sharper majorants as well.
-/

/-- The full diagonal Euler factor. -/
noncomputable def diagonalEuler
    (u v : ArithmeticFunction ℝ) (p : ℕ) : ℝ :=
  ∑' j : ℕ, u (p ^ j) * v (p ^ j) / ((p ^ j : ℕ) : ℝ)

/-- The full shifted local Euler factor. -/
noncomputable def shiftedEuler
    (u v : ArithmeticFunction ℝ) (p i : ℕ) : ℝ :=
  ∑' j : ℕ, u (p ^ (i + j)) * v (p ^ j) / ((p ^ j : ℕ) : ℝ)

/-- The full weighted numerator used in `w(p^i)`. -/
noncomputable def weightedShiftedEuler
    (u v : ArithmeticFunction ℝ) (p i : ℕ) : ℝ :=
  ∑' j : ℕ,
    u (p ^ (i + j)) * v (p ^ j) *
      (1 + (j : ℝ) * Real.log (p : ℝ)) /
      ((p ^ j : ℕ) : ℝ)

/-- The correction factor in the published statement of Lemma 2. -/
noncomputable def eulerCorrection
    (u v : ArithmeticFunction ℝ) (p i : ℕ) : ℝ :=
  weightedShiftedEuler u v p i / diagonalEuler u v p

lemma diagonalEuler_pos
    (u v : ArithmeticFunction ℝ)
    (hu_one : u 1 = 1) (hv_one : v 1 = 1)
    (hu : ∀ n, 0 ≤ u n) (hv : ∀ n, 0 ≤ v n)
    (p : ℕ)
    (hsum : Summable (fun j : ℕ =>
      u (p ^ j) * v (p ^ j) / ((p ^ j : ℕ) : ℝ))) :
    0 < diagonalEuler u v p := by
  let a : ℕ → ℝ := fun j =>
    u (p ^ j) * v (p ^ j) / ((p ^ j : ℕ) : ℝ)
  have ha_nonneg : ∀ j, 0 ≤ a j := fun j =>
    div_nonneg (mul_nonneg (hu _) (hv _)) (Nat.cast_nonneg _)
  have hsingle : (∑ j ∈ ({0} : Finset ℕ), a j) ≤ ∑' j, a j :=
    hsum.sum_le_tsum {0} (fun j hj => ha_nonneg j)
  have ha0 : a 0 = 1 := by simp [a, hu_one, hv_one]
  have : (1 : ℝ) ≤ ∑' j, a j := by simpa [ha0] using hsingle
  change 0 < ∑' j, a j
  linarith

lemma shiftedEuler_nonneg
    (u v : ArithmeticFunction ℝ)
    (hu : ∀ n, 0 ≤ u n) (hv : ∀ n, 0 ≤ v n)
    (p i : ℕ) :
    0 ≤ shiftedEuler u v p i := by
  unfold shiftedEuler
  exact tsum_nonneg fun j =>
    div_nonneg (mul_nonneg (hu _) (hv _)) (Nat.cast_nonneg _)

lemma weightedShiftedEuler_nonneg
    (u v : ArithmeticFunction ℝ)
    (hu : ∀ n, 0 ≤ u n) (hv : ∀ n, 0 ≤ v n)
    {p : ℕ} (hp : p.Prime) (i : ℕ) :
    0 ≤ weightedShiftedEuler u v p i := by
  unfold weightedShiftedEuler
  refine tsum_nonneg fun j => div_nonneg ?_ (Nat.cast_nonneg _)
  have hlog : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  exact mul_nonneg (mul_nonneg (hu _) (hv _)) (by positivity)

lemma shiftedEuler_le_weightedShiftedEuler
    (u v : ArithmeticFunction ℝ)
    (hu : ∀ n, 0 ≤ u n) (hv : ∀ n, 0 ≤ v n)
    {p : ℕ} (hp : p.Prime) (i : ℕ)
    (hshift : Summable (fun j : ℕ =>
      u (p ^ (i + j)) * v (p ^ j) / ((p ^ j : ℕ) : ℝ)))
    (hweighted : Summable (fun j : ℕ =>
      u (p ^ (i + j)) * v (p ^ j) *
        (1 + (j : ℝ) * Real.log (p : ℝ)) /
        ((p ^ j : ℕ) : ℝ))) :
    shiftedEuler u v p i ≤ weightedShiftedEuler u v p i := by
  unfold shiftedEuler weightedShiftedEuler
  apply hshift.tsum_le_tsum
  · intro j
    have hpow_pos : 0 < p ^ j := pow_pos hp.pos j
    have hdenom_pos : 0 < (((p ^ j : ℕ) : ℝ)) := by exact_mod_cast hpow_pos
    have hbase : 0 ≤ u (p ^ (i + j)) * v (p ^ j) :=
      mul_nonneg (hu _) (hv _)
    have hlog : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
    apply (div_le_div_iff_of_pos_right hdenom_pos).2
    nlinarith [mul_nonneg (Nat.cast_nonneg j) hlog]
  · exact hweighted

lemma shiftedEuler_le_correction_mul_diagonal
    (u v : ArithmeticFunction ℝ)
    (hu_one : u 1 = 1) (hv_one : v 1 = 1)
    (hu : ∀ n, 0 ≤ u n) (hv : ∀ n, 0 ≤ v n)
    {p : ℕ} (hp : p.Prime) (i : ℕ)
    (hdiag : Summable (fun j : ℕ =>
      u (p ^ j) * v (p ^ j) / ((p ^ j : ℕ) : ℝ)))
    (hshift : Summable (fun j : ℕ =>
      u (p ^ (i + j)) * v (p ^ j) / ((p ^ j : ℕ) : ℝ)))
    (hweighted : Summable (fun j : ℕ =>
      u (p ^ (i + j)) * v (p ^ j) *
        (1 + (j : ℝ) * Real.log (p : ℝ)) /
        ((p ^ j : ℕ) : ℝ))) :
    shiftedEuler u v p i ≤
      eulerCorrection u v p i * diagonalEuler u v p := by
  have hdiag_ne : diagonalEuler u v p ≠ 0 :=
    ne_of_gt (diagonalEuler_pos u v hu_one hv_one hu hv p hdiag)
  rw [eulerCorrection, div_mul_cancel₀ _ hdiag_ne]
  exact shiftedEuler_le_weightedShiftedEuler u v hu hv hp i hshift hweighted

lemma eulerCorrection_nonneg
    (u v : ArithmeticFunction ℝ)
    (hu_one : u 1 = 1) (hv_one : v 1 = 1)
    (hu : ∀ n, 0 ≤ u n) (hv : ∀ n, 0 ≤ v n)
    {p : ℕ} (hp : p.Prime) (i : ℕ)
    (hdiag : Summable (fun j : ℕ =>
      u (p ^ j) * v (p ^ j) / ((p ^ j : ℕ) : ℝ))) :
    0 ≤ eulerCorrection u v p i := by
  exact div_nonneg
    (weightedShiftedEuler_nonneg u v hu hv hp i)
    (diagonalEuler_pos u v hu_one hv_one hu hv p hdiag).le

/-- The prime-power hypothesis in Lemma 2 makes both local series absolutely
summable.  This is the geometric-tail calculation used to discharge the
summability arguments of the infinite-series interface below. -/
lemma localSeries_summable_of_prime_power_geometric
    (u v : ArithmeticFunction ℝ)
    {p : ℕ} (hp : p.Prime) (i : ℕ)
    (lambda_i lambda : ℝ)
    (hlambda_i : 0 ≤ lambda_i) (hlambda : 0 ≤ lambda)
    (hlambda_lt : lambda < 2)
    (hlower : ∀ j : ℕ, 0 ≤ u (p ^ (i + j)) * v (p ^ j))
    (hupper : ∀ j : ℕ,
      u (p ^ (i + j)) * v (p ^ j) ≤ lambda_i * lambda ^ j) :
    Summable (fun j : ℕ =>
      u (p ^ (i + j)) * v (p ^ j) / ((p ^ j : ℕ) : ℝ)) ∧
    Summable (fun j : ℕ =>
      u (p ^ (i + j)) * v (p ^ j) *
        (1 + (j : ℝ) * Real.log (p : ℝ)) /
        ((p ^ j : ℕ) : ℝ)) := by
  let r : ℝ := lambda / (p : ℝ)
  have hpcast : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hpcast_pos : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hr_nonneg : 0 ≤ r := div_nonneg hlambda hpcast_pos.le
  have hr_lt : r < 1 := by
    dsimp [r]
    exact (div_lt_one hpcast_pos).2 (hlambda_lt.trans_le hpcast)
  have hrnorm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr_nonneg]
    exact hr_lt
  have hgeom : Summable (fun j : ℕ => r ^ j) :=
    summable_geometric_of_lt_one hr_nonneg hr_lt
  have hjgeom : Summable (fun j : ℕ => (j : ℝ) * r ^ j) := by
    simpa using
      (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hrnorm)
  have hplain_major : Summable (fun j : ℕ => lambda_i * r ^ j) :=
    hgeom.mul_left lambda_i
  have hplain_le : ∀ j : ℕ,
      u (p ^ (i + j)) * v (p ^ j) / ((p ^ j : ℕ) : ℝ) ≤
        lambda_i * r ^ j := by
    intro j
    have hpow_pos : 0 < p ^ j := pow_pos hp.pos j
    have hdenom_pos : 0 < (((p ^ j : ℕ) : ℝ)) := by exact_mod_cast hpow_pos
    calc
      u (p ^ (i + j)) * v (p ^ j) / ((p ^ j : ℕ) : ℝ)
          ≤ (lambda_i * lambda ^ j) / ((p ^ j : ℕ) : ℝ) :=
            div_le_div_of_nonneg_right (hupper j) hdenom_pos.le
      _ = lambda_i * r ^ j := by
        simp only [Nat.cast_pow]
        rw [show r ^ j = lambda ^ j / (p : ℝ) ^ j by simp [r, div_pow]]
        ring
  have hplain : Summable (fun j : ℕ =>
      u (p ^ (i + j)) * v (p ^ j) / ((p ^ j : ℕ) : ℝ)) :=
    Summable.of_nonneg_of_le
      (fun j => div_nonneg (hlower j) (Nat.cast_nonneg _))
      hplain_le hplain_major
  have hlog_nonneg : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hweighted_major : Summable (fun j : ℕ =>
      lambda_i * r ^ j * (1 + (j : ℝ) * Real.log (p : ℝ))) := by
    have hadd : Summable (fun j : ℕ =>
        r ^ j + Real.log (p : ℝ) * ((j : ℝ) * r ^ j)) :=
      hgeom.add (hjgeom.mul_left (Real.log (p : ℝ)))
    exact (hadd.mul_left lambda_i).congr (fun j => by ring)
  have hweighted_le : ∀ j : ℕ,
      u (p ^ (i + j)) * v (p ^ j) *
          (1 + (j : ℝ) * Real.log (p : ℝ)) /
          ((p ^ j : ℕ) : ℝ) ≤
        lambda_i * r ^ j *
          (1 + (j : ℝ) * Real.log (p : ℝ)) := by
    intro j
    have hpow_pos : 0 < p ^ j := pow_pos hp.pos j
    have hdenom_pos : 0 < (((p ^ j : ℕ) : ℝ)) := by exact_mod_cast hpow_pos
    have hweight : 0 ≤ 1 + (j : ℝ) * Real.log (p : ℝ) := by positivity
    calc
      u (p ^ (i + j)) * v (p ^ j) *
            (1 + (j : ℝ) * Real.log (p : ℝ)) /
            ((p ^ j : ℕ) : ℝ)
          ≤ (lambda_i * lambda ^ j) *
              (1 + (j : ℝ) * Real.log (p : ℝ)) /
              ((p ^ j : ℕ) : ℝ) := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right (hupper j) hweight) hdenom_pos.le
      _ = lambda_i * r ^ j *
            (1 + (j : ℝ) * Real.log (p : ℝ)) := by
        simp only [Nat.cast_pow]
        rw [show r ^ j = lambda ^ j / (p : ℝ) ^ j by simp [r, div_pow]]
        ring
  have hweighted : Summable (fun j : ℕ =>
      u (p ^ (i + j)) * v (p ^ j) *
        (1 + (j : ℝ) * Real.log (p : ℝ)) /
        ((p ^ j : ℕ) : ℝ)) :=
    Summable.of_nonneg_of_le
      (fun j => div_nonneg
        (mul_nonneg (hlower j) (by positivity)) (Nat.cast_nonneg _))
      hweighted_le hweighted_major
  exact ⟨hplain, hweighted⟩

/-- Raw full Euler product before local replacement. -/
noncomputable def basicInfiniteShiftedEulerProduct
    (u v : ArithmeticFunction ℝ) (k N : ℕ) : ℝ :=
  ∏ p ∈ (N + 1).primesBelow,
    if p ∈ k.primeFactors then
      shiftedEuler u v p (k.factorization p)
    else
      diagonalEuler u v p

/-- Full correction times the common diagonal Euler product. -/
noncomputable def correctedInfiniteEulerProduct
    (u v : ArithmeticFunction ℝ) (k N : ℕ) : ℝ :=
  (∏ p ∈ k.primeFactors ∩ (N + 1).primesBelow,
      eulerCorrection u v p (k.factorization p)) *
    ∏ p ∈ (N + 1).primesBelow, diagonalEuler u v p

lemma basicInfiniteShiftedEulerProduct_le_correctedInfiniteEulerProduct
    (u v : ArithmeticFunction ℝ)
    (hu_one : u 1 = 1) (hv_one : v 1 = 1)
    (hu : ∀ n, 0 ≤ u n) (hv : ∀ n, 0 ≤ v n)
    (k N : ℕ)
    (hdiag : ∀ p ∈ (N + 1).primesBelow,
      Summable (fun j : ℕ =>
        u (p ^ j) * v (p ^ j) / ((p ^ j : ℕ) : ℝ)))
    (hshift : ∀ p ∈ k.primeFactors ∩ (N + 1).primesBelow,
      Summable (fun j : ℕ =>
        u (p ^ (k.factorization p + j)) * v (p ^ j) /
          ((p ^ j : ℕ) : ℝ)))
    (hweighted : ∀ p ∈ k.primeFactors ∩ (N + 1).primesBelow,
      Summable (fun j : ℕ =>
        u (p ^ (k.factorization p + j)) * v (p ^ j) *
          (1 + (j : ℝ) * Real.log (p : ℝ)) /
          ((p ^ j : ℕ) : ℝ))) :
    basicInfiniteShiftedEulerProduct u v k N ≤
      correctedInfiniteEulerProduct u v k N := by
  classical
  let S := (N + 1).primesBelow
  let T := k.primeFactors ∩ S
  have hTS : T ⊆ S := Finset.inter_subset_right
  have hprime : ∀ p ∈ S, p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primesBelow hp
  have hreplace := product_replace_on_subset hTS
    (fun p => shiftedEuler u v p (k.factorization p))
    (fun p => diagonalEuler u v p)
    (fun p => eulerCorrection u v p (k.factorization p))
    (fun p hp => (diagonalEuler_pos u v hu_one hv_one hu hv p
      (hdiag p (by simpa [S] using hp))).le)
    (fun p hp => shiftedEuler_nonneg u v hu hv p (k.factorization p))
    (fun p hp => eulerCorrection_nonneg u v hu_one hv_one hu hv
      (hprime p (hTS hp)) (k.factorization p)
      (hdiag p (by simpa [S] using hTS hp)))
    (fun p hp => shiftedEuler_le_correction_mul_diagonal
      u v hu_one hv_one hu hv (hprime p (hTS hp)) (k.factorization p)
      (hdiag p (by simpa [S] using hTS hp))
      (hshift p (by simpa [T] using hp))
      (hweighted p (by simpa [T] using hp)))
  have hleft : basicInfiniteShiftedEulerProduct u v k N =
      ∏ p ∈ S,
        if p ∈ T then shiftedEuler u v p (k.factorization p)
        else diagonalEuler u v p := by
    unfold basicInfiniteShiftedEulerProduct
    dsimp [S]
    apply Finset.prod_congr rfl
    intro p hp
    have hpS : p ∈ S := by simpa [S] using hp
    simp only [T, Finset.mem_inter, hpS, and_true]
  rw [hleft]
  simpa [correctedInfiniteEulerProduct, S, T] using hreplace

/-- Literal infinite-series version of the Lemma 2 local-factor conclusion,
again parameterized only by the raw Halberstam--Richert engine output. -/
theorem multiplicative_convolution_mean_value_II_infinite_of_basic_engine
    (u v : ArithmeticFunction ℝ)
    (hu_one : u 1 = 1) (hv_one : v 1 = 1)
    (hu : ∀ n, 0 ≤ u n) (hv : ∀ n, 0 ≤ v n)
    (k N : ℕ) (scale : ℝ) (hscale : 0 ≤ scale)
    (hdiag : ∀ p ∈ (N + 1).primesBelow,
      Summable (fun j : ℕ =>
        u (p ^ j) * v (p ^ j) / ((p ^ j : ℕ) : ℝ)))
    (hshift : ∀ p ∈ k.primeFactors ∩ (N + 1).primesBelow,
      Summable (fun j : ℕ =>
        u (p ^ (k.factorization p + j)) * v (p ^ j) /
          ((p ^ j : ℕ) : ℝ)))
    (hweighted : ∀ p ∈ k.primeFactors ∩ (N + 1).primesBelow,
      Summable (fun j : ℕ =>
        u (p ^ (k.factorization p + j)) * v (p ^ j) *
          (1 + (j : ℝ) * Real.log (p : ℝ)) /
          ((p ^ j : ℕ) : ℝ)))
    (hengine : shiftedConvolutionSum u v k N ≤
      scale * basicInfiniteShiftedEulerProduct u v k N *
        largePrimeShiftProduct u k N) :
    shiftedConvolutionSum u v k N ≤
      scale * correctedInfiniteEulerProduct u v k N *
        largePrimeShiftProduct u k N := by
  have heuler := basicInfiniteShiftedEulerProduct_le_correctedInfiniteEulerProduct
    u v hu_one hv_one hu hv k N hdiag hshift hweighted
  have htail := largePrimeShiftProduct_nonneg u hu k N
  exact hengine.trans <|
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left heuler hscale) htail

/-! ## The normalized shifted multiplicative function

For positive `u k`, the quotient

`h_k(n) = u(k*n) * v(n) / u(k)`

is multiplicative as a function of `n`.  The key identity is the standard
gcd--lcm identity for a multiplicative function, applied to `k*a` and `k*b`.
This is the function to which the unconditional Halberstam--Richert theorem
is applied in order to produce the previously isolated `hengine`.
-/

/-- The normalized shifted weight used in the proof of Lemma 2. -/
noncomputable def normalizedShift
    (u v : ArithmeticFunction ℝ) (k : ℕ) : ArithmeticFunction ℝ where
  toFun n := u (k * n) * v n / u k
  map_zero' := by simp

@[simp] lemma normalizedShift_apply
    (u v : ArithmeticFunction ℝ) (k n : ℕ) :
    normalizedShift u v k n = u (k * n) * v n / u k := rfl

lemma normalizedShift_one
    (u v : ArithmeticFunction ℝ)
    (hv_one : v 1 = 1) {k : ℕ} (huk : u k ≠ 0) :
    normalizedShift u v k 1 = 1 := by
  simp [normalizedShift_apply, hv_one, huk]

lemma multiplicative_shift_identity
    (u : ArithmeticFunction ℝ) (hu : u.IsMultiplicative)
    {k a b : ℕ} (hab : a.Coprime b) :
    u (k * a) * u (k * b) = u k * u (k * (a * b)) := by
  have h := hu.lcm_apply_mul_gcd_apply (x := k * a) (y := k * b)
  have hgcd : (k * a).gcd (k * b) = k := by
    calc
      (k * a).gcd (k * b) = k * a.gcd b := by
        exact Nat.gcd_mul_left k a b
      _ = k := by rw [hab.gcd_eq_one, mul_one]
  have hlcm : (k * a).lcm (k * b) = k * (a * b) := by
    calc
      (k * a).lcm (k * b) = k * a.lcm b := by
        exact Nat.lcm_mul_left k a b
      _ = k * (a * b) := by rw [hab.lcm_eq_mul]
  rw [hgcd, hlcm] at h
  nlinarith

lemma normalizedShift_isMultiplicative
    (u v : ArithmeticFunction ℝ)
    (hu : u.IsMultiplicative) (hv : v.IsMultiplicative)
    {k : ℕ} (huk : u k ≠ 0) :
    (normalizedShift u v k).IsMultiplicative := by
  refine ⟨normalizedShift_one u v hv.map_one huk, ?_⟩
  intro a b hab
  rw [normalizedShift_apply, normalizedShift_apply, normalizedShift_apply,
    hv.map_mul_of_coprime hab]
  have hU := multiplicative_shift_identity u hu (k := k) hab
  field_simp [huk]
  calc
    u (k * (a * b)) * v a * v b * u k =
        (u k * u (k * (a * b))) * (v a * v b) := by ring
    _ = (u (k * a) * u (k * b)) * (v a * v b) := by rw [hU]
    _ = v a * v b * u (k * a) * u (k * b) := by ring

lemma normalizedShift_nonneg
    (u v : ArithmeticFunction ℝ)
    (hu : ∀ n, 0 ≤ u n) (hv : ∀ n, 0 ≤ v n)
    {k : ℕ} (huk : 0 < u k) (n : ℕ) :
    0 ≤ normalizedShift u v k n := by
  exact div_nonneg (mul_nonneg (hu _) (hv _)) huk.le

/-- Removing the complete `p`-part of `k` gives the expected local quotient
formula for a prime power of the normalized shift. -/
lemma normalizedShift_prime_power
    (u v : ArithmeticFunction ℝ)
    (hu : u.IsMultiplicative)
    {k p j : ℕ} (hk : k ≠ 0) (hp : p.Prime)
    (hu_pos : ∀ n, n ≠ 0 → 0 < u n) :
    normalizedShift u v k (p ^ j) =
      u (p ^ (k.factorization p + j)) * v (p ^ j) /
        u (p ^ (k.factorization p)) := by
  let m := ordCompl[p] k
  have hm : m ≠ 0 := (Nat.ordCompl_pos p hk).ne'
  have hcop : (p ^ k.factorization p).Coprime m :=
    (Nat.coprime_ordCompl hp hk).pow_left _
  have hcop' : m.Coprime (p ^ (k.factorization p + j)) :=
    (Nat.coprime_ordCompl hp hk).symm.pow_right _
  have hkdecomp : p ^ k.factorization p * m = k :=
    Nat.ordProj_mul_ordCompl_eq_self k p
  have hkpdecomp : k * p ^ j = m * p ^ (k.factorization p + j) := by
    calc
      k * p ^ j = (p ^ k.factorization p * m) * p ^ j := by rw [hkdecomp]
      _ = m * p ^ (k.factorization p + j) := by rw [pow_add]; ring
  have hu_k : u k = u (p ^ k.factorization p) * u m := by
    calc
      u k = u (p ^ k.factorization p * m) := by rw [hkdecomp]
      _ = u (p ^ k.factorization p) * u m := hu.map_mul_of_coprime hcop
  have hu_kp : u (k * p ^ j) =
      u m * u (p ^ (k.factorization p + j)) := by
    rw [hkpdecomp, hu.map_mul_of_coprime hcop']
  have hum : u m ≠ 0 := ne_of_gt (hu_pos m hm)
  have huppi : u (p ^ k.factorization p) ≠ 0 :=
    ne_of_gt (hu_pos _ (pow_ne_zero _ hp.ne_zero))
  rw [normalizedShift_apply, hu_k, hu_kp]
  field_simp [hum, huppi]

lemma shiftedEuler_zero
    (u v : ArithmeticFunction ℝ) (p : ℕ) :
    shiftedEuler u v p 0 = diagonalEuler u v p := by
  simp [shiftedEuler, diagonalEuler]

lemma normalizedShift_eulerFactor
    (u v : ArithmeticFunction ℝ)
    (hu : u.IsMultiplicative)
    {k p : ℕ} (hk : k ≠ 0) (hp : p.Prime)
    (hu_pos : ∀ n, n ≠ 0 → 0 < u n) :
    (∑' j : ℕ,
      normalizedShift u v k (p ^ j) / ((p ^ j : ℕ) : ℝ)) =
      shiftedEuler u v p (k.factorization p) /
        u (p ^ (k.factorization p)) := by
  unfold shiftedEuler
  rw [← tsum_div_const]
  apply tsum_congr
  intro j
  rw [normalizedShift_prime_power u v hu hk hp hu_pos]
  ring

lemma multiplicative_value_split_at_primes
    (u : ArithmeticFunction ℝ) (hu : u.IsMultiplicative)
    {k : ℕ} (hk : k ≠ 0) (P : Finset ℕ) :
    u k =
      (∏ p ∈ k.primeFactors ∩ P, u (p ^ (k.factorization p))) *
      ∏ p ∈ k.primeFactors \ P, u (p ^ (k.factorization p)) := by
  classical
  let T := k.primeFactors ∩ P
  let R := k.primeFactors \ P
  have hdis : Disjoint T R := by
    rw [Finset.disjoint_left]
    intro p hpT hpR
    exact (Finset.mem_sdiff.mp hpR).2 (Finset.mem_inter.mp hpT).2
  have hunion : T ∪ R = k.primeFactors := by
    ext p
    simp only [T, R, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hfac := hu.multiplicative_factorization u hk
  change u k =
    (∏ p ∈ T, u (p ^ (k.factorization p))) *
      ∏ p ∈ R, u (p ^ (k.factorization p))
  calc
    u k = ∏ p ∈ k.primeFactors, u (p ^ (k.factorization p)) := hfac
    _ = ∏ p ∈ T ∪ R, u (p ^ (k.factorization p)) := by rw [hunion]
    _ = (∏ p ∈ T, u (p ^ (k.factorization p))) *
        ∏ p ∈ R, u (p ^ (k.factorization p)) :=
      Finset.prod_union hdis

lemma prime_factor_denominator_product
    (u : ArithmeticFunction ℝ) (hu : u.IsMultiplicative)
    (k : ℕ) (P : Finset ℕ) :
    (∏ p ∈ P, u (p ^ (k.factorization p))) =
      ∏ p ∈ k.primeFactors ∩ P, u (p ^ (k.factorization p)) := by
  classical
  symm
  apply Finset.prod_subset Finset.inter_subset_right
  intro p hpP hpnot
  have hpnotfac : p ∉ k.primeFactors := by
    intro hpfac
    exact hpnot (Finset.mem_inter.mpr ⟨hpfac, hpP⟩)
  have hzero : k.factorization p = 0 := by
    exact Finsupp.notMem_support_iff.mp hpnotfac
  simp [hzero, hu.map_one]

lemma basicInfiniteShiftedEulerProduct_eq_unconditional_product
    (u v : ArithmeticFunction ℝ) (hu : u.IsMultiplicative)
    (k N : ℕ) :
    basicInfiniteShiftedEulerProduct u v k N =
      ∏ p ∈ (N + 1).primesBelow,
        shiftedEuler u v p (k.factorization p) := by
  classical
  unfold basicInfiniteShiftedEulerProduct
  apply Finset.prod_congr rfl
  intro p hpP
  by_cases hpk : p ∈ k.primeFactors
  · simp [hpk]
  · have hzero : k.factorization p = 0 := by
      exact Finsupp.notMem_support_iff.mp hpk
    simp [hpk, hzero, shiftedEuler_zero]

/-- Euler product of the normalized shifted multiplicative function. -/
noncomputable def normalizedShiftEulerProduct
    (u v : ArithmeticFunction ℝ) (k N : ℕ) : ℝ :=
  ∏ p ∈ (N + 1).primesBelow,
    ∑' j : ℕ,
      normalizedShift u v k (p ^ j) / ((p ^ j : ℕ) : ℝ)

/-- Multiplication by `u(k)` cancels the local normalizing denominators.  The
uncancelled primes outside the Euler-product range are exactly the published
large-prime shift factor. -/
lemma normalizedShiftEulerProduct_cancellation
    (u v : ArithmeticFunction ℝ)
    (hu : u.IsMultiplicative)
    {k : ℕ} (hk : k ≠ 0)
    (hu_pos : ∀ n, n ≠ 0 → 0 < u n)
    (N : ℕ) :
    u k * normalizedShiftEulerProduct u v k N =
      basicInfiniteShiftedEulerProduct u v k N *
        largePrimeShiftProduct u k N := by
  classical
  let P := (N + 1).primesBelow
  let T := k.primeFactors ∩ P
  let U : ℕ → ℝ := fun p => u (p ^ (k.factorization p))
  let A : ℕ → ℝ := fun p => shiftedEuler u v p (k.factorization p)
  have hpprime : ∀ p ∈ P, p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primesBelow (by simpa [P] using hp)
  have hnorm : normalizedShiftEulerProduct u v k N =
      (∏ p ∈ P, A p) / ∏ p ∈ P, U p := by
    unfold normalizedShiftEulerProduct
    change (∏ p ∈ P,
      ∑' j : ℕ,
        normalizedShift u v k (p ^ j) / ((p ^ j : ℕ) : ℝ)) = _
    calc
      (∏ p ∈ P,
          ∑' j : ℕ,
            normalizedShift u v k (p ^ j) / ((p ^ j : ℕ) : ℝ)) =
          ∏ p ∈ P, A p / U p := by
            apply Finset.prod_congr rfl
            intro p hpP
            exact normalizedShift_eulerFactor u v hu hk (hpprime p hpP) hu_pos
      _ = (∏ p ∈ P, A p) / ∏ p ∈ P, U p := by
        rw [Finset.prod_div_distrib]
  have hdenom : (∏ p ∈ P, U p) = ∏ p ∈ T, U p := by
    simpa [P, T, U] using prime_factor_denominator_product u hu k P
  have hsplit : u k =
      (∏ p ∈ T, U p) *
        ∏ p ∈ k.primeFactors \ P, U p := by
    simpa [P, T, U] using multiplicative_value_split_at_primes u hu hk P
  have hbasic : basicInfiniteShiftedEulerProduct u v k N =
      ∏ p ∈ P, A p := by
    simpa [P, A] using
      basicInfiniteShiftedEulerProduct_eq_unconditional_product u v hu k N
  have hTpos : 0 < ∏ p ∈ T, U p := by
    refine Finset.prod_pos fun p hpT => ?_
    exact hu_pos _ (pow_ne_zero _ (Nat.prime_of_mem_primeFactors
      (Finset.mem_inter.mp hpT).1).ne_zero)
  rw [hnorm, hdenom, hsplit, hbasic]
  unfold largePrimeShiftProduct
  change ((∏ p ∈ T, U p) *
      ∏ p ∈ k.primeFactors \ P, U p) *
      ((∏ p ∈ P, A p) / ∏ p ∈ T, U p) =
    (∏ p ∈ P, A p) *
      ∏ p ∈ k.primeFactors \ P, U p
  field_simp [ne_of_gt hTpos]

lemma shiftedConvolutionSum_eq_mul_normalizedPartialSum
    (u v : ArithmeticFunction ℝ) {k : ℕ} (huk : u k ≠ 0) (N : ℕ) :
    shiftedConvolutionSum u v k N =
      u k * HalberstamScratch.partialSum (normalizedShift u v k) N := by
  unfold shiftedConvolutionSum HalberstamScratch.partialSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [normalizedShift_apply]
  field_simp [huk]

/-- The raw `hengine` in Erdős--Tenenbaum Lemma 2, now obtained
unconditionally from the explicit Halberstam--Richert Lemma 1 theorem.

The local prime-power hypothesis is stated directly for the normalized
shift.  This is the form needed in the weighted divisor applications: after
choosing `u` and `v`, it is discharged by a one-line calculation on prime
powers. -/
theorem raw_multiplicative_convolution_engine
    (u v : ArithmeticFunction ℝ)
    (hu : u.IsMultiplicative) (hv : v.IsMultiplicative)
    (hu_nonneg : ∀ n, 0 ≤ u n) (hv_nonneg : ∀ n, 0 ≤ v n)
    (hu_pos : ∀ n, n ≠ 0 → 0 < u n)
    {k : ℕ} (hk : k ≠ 0)
    (lambda1 lambda2 : ℝ)
    (hlambda1 : 0 ≤ lambda1)
    (hlambda2 : 0 ≤ lambda2) (hlambda2_lt : lambda2 < 2)
    (hpow : ∀ (p : ℕ), p.Prime → ∀ j : ℕ,
      u (p ^ (k.factorization p + (j + 1))) * v (p ^ (j + 1)) /
          u (p ^ (k.factorization p)) ≤
        lambda1 * lambda2 ^ j)
    (N : ℕ) (hN : 2 ≤ N) :
    shiftedConvolutionSum u v k N ≤
      (HalberstamScratch.explicitMassConstant lambda1 lambda2 + 1) *
        (N : ℝ) / Real.log (N : ℝ) *
          basicInfiniteShiftedEulerProduct u v k N *
            largePrimeShiftProduct u k N := by
  let h : ArithmeticFunction ℝ := normalizedShift u v k
  have huk : 0 < u k := hu_pos k hk
  have hh_mult : h.IsMultiplicative :=
    normalizedShift_isMultiplicative u v hu hv huk.ne'
  have hh_nonneg : ∀ n, 0 ≤ h n :=
    normalizedShift_nonneg u v hu_nonneg hv_nonneg huk
  have hh_pow : ∀ (p : ℕ), p.Prime → ∀ j : ℕ,
      h (p ^ (j + 1)) ≤ lambda1 * lambda2 ^ j := by
    intro p hp j
    rw [show h (p ^ (j + 1)) =
        u (p ^ (k.factorization p + (j + 1))) * v (p ^ (j + 1)) /
          u (p ^ k.factorization p) by
      exact normalizedShift_prime_power u v hu hk hp hu_pos]
    exact hpow p hp j
  have hHR := HalberstamComplete448.halberstam_richert_explicit
    h (by simp [h]) (by simpa [h] using hh_mult.map_one)
    (fun {_ _} hcop => hh_mult.map_mul_of_coprime hcop)
    hh_nonneg lambda1 lambda2 hlambda1 hlambda2 hlambda2_lt
    hh_pow N hN
  have hsum := shiftedConvolutionSum_eq_mul_normalizedPartialSum
    u v huk.ne' N
  have hcancel := normalizedShiftEulerProduct_cancellation
    u v hu hk hu_pos N
  change HalberstamScratch.partialSum h N ≤
      (HalberstamScratch.explicitMassConstant lambda1 lambda2 + 1) *
        (N : ℝ) / Real.log (N : ℝ) *
          normalizedShiftEulerProduct u v k N at hHR
  calc
    shiftedConvolutionSum u v k N =
        u k * HalberstamScratch.partialSum h N := hsum
    _ ≤ u k *
        ((HalberstamScratch.explicitMassConstant lambda1 lambda2 + 1) *
          (N : ℝ) / Real.log (N : ℝ) *
            normalizedShiftEulerProduct u v k N) :=
      mul_le_mul_of_nonneg_left hHR huk.le
    _ = (HalberstamScratch.explicitMassConstant lambda1 lambda2 + 1) *
        (N : ℝ) / Real.log (N : ℝ) *
          basicInfiniteShiftedEulerProduct u v k N *
            largePrimeShiftProduct u k N := by
      calc
        u k *
            ((HalberstamScratch.explicitMassConstant lambda1 lambda2 + 1) *
              (N : ℝ) / Real.log (N : ℝ) *
                normalizedShiftEulerProduct u v k N) =
            ((HalberstamScratch.explicitMassConstant lambda1 lambda2 + 1) *
              (N : ℝ) / Real.log (N : ℝ)) *
                (u k * normalizedShiftEulerProduct u v k N) := by ring
        _ = ((HalberstamScratch.explicitMassConstant lambda1 lambda2 + 1) *
              (N : ℝ) / Real.log (N : ℝ)) *
                (basicInfiniteShiftedEulerProduct u v k N *
                  largePrimeShiftProduct u k N) := by rw [hcancel]
        _ = _ := by ring

/-- Unconditional infinite-series Erdős--Tenenbaum Lemma 2, obtained by
combining `raw_multiplicative_convolution_engine` with the proved local-factor
replacement.  The three summability hypotheses are local consequences of the
geometric prime-power majorants; `localSeries_summable_of_prime_power_geometric`
is provided above for that purpose. -/
theorem multiplicative_convolution_mean_value_II
    (u v : ArithmeticFunction ℝ)
    (hu : u.IsMultiplicative) (hv : v.IsMultiplicative)
    (hu_one : u 1 = 1) (hv_one : v 1 = 1)
    (hu_nonneg : ∀ n, 0 ≤ u n) (hv_nonneg : ∀ n, 0 ≤ v n)
    (hu_pos : ∀ n, n ≠ 0 → 0 < u n)
    {k : ℕ} (hk : k ≠ 0)
    (lambda1 lambda2 : ℝ)
    (hlambda1 : 0 ≤ lambda1)
    (hlambda2 : 0 ≤ lambda2) (hlambda2_lt : lambda2 < 2)
    (hpow : ∀ (p : ℕ), p.Prime → ∀ j : ℕ,
      u (p ^ (k.factorization p + (j + 1))) * v (p ^ (j + 1)) /
          u (p ^ (k.factorization p)) ≤
        lambda1 * lambda2 ^ j)
    (N : ℕ) (hN : 2 ≤ N)
    (hdiag : ∀ p ∈ (N + 1).primesBelow,
      Summable (fun j : ℕ =>
        u (p ^ j) * v (p ^ j) / ((p ^ j : ℕ) : ℝ)))
    (hshift : ∀ p ∈ k.primeFactors ∩ (N + 1).primesBelow,
      Summable (fun j : ℕ =>
        u (p ^ (k.factorization p + j)) * v (p ^ j) /
          ((p ^ j : ℕ) : ℝ)))
    (hweighted : ∀ p ∈ k.primeFactors ∩ (N + 1).primesBelow,
      Summable (fun j : ℕ =>
        u (p ^ (k.factorization p + j)) * v (p ^ j) *
          (1 + (j : ℝ) * Real.log (p : ℝ)) /
          ((p ^ j : ℕ) : ℝ))) :
    shiftedConvolutionSum u v k N ≤
      (HalberstamScratch.explicitMassConstant lambda1 lambda2 + 1) *
        (N : ℝ) / Real.log (N : ℝ) *
          correctedInfiniteEulerProduct u v k N *
            largePrimeShiftProduct u k N := by
  let scale : ℝ :=
    (HalberstamScratch.explicitMassConstant lambda1 lambda2 + 1) *
      (N : ℝ) / Real.log (N : ℝ)
  have hscale : 0 ≤ scale := by
    dsimp [scale]
    exact div_nonneg
      (mul_nonneg
        (by
          have := HalberstamScratch.explicitMassConstant_nonneg
            hlambda1 hlambda2
          linarith)
        (Nat.cast_nonneg N))
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega)))
  apply multiplicative_convolution_mean_value_II_infinite_of_basic_engine
    u v hu_one hv_one hu_nonneg hv_nonneg k N scale hscale
    hdiag hshift hweighted
  dsimp [scale]
  exact raw_multiplicative_convolution_engine
    u v hu hv hu_nonneg hv_nonneg hu_pos hk
    lambda1 lambda2 hlambda1 hlambda2 hlambda2_lt hpow N hN

/-- A fully prime-power-facing wrapper: the standard geometric majorant
automatically supplies every local summability hypothesis in
`multiplicative_convolution_mean_value_II`. -/
theorem multiplicative_convolution_mean_value_II_of_geometric_majorants
    (u v : ArithmeticFunction ℝ)
    (hu : u.IsMultiplicative) (hv : v.IsMultiplicative)
    (hu_one : u 1 = 1) (hv_one : v 1 = 1)
    (hu_nonneg : ∀ n, 0 ≤ u n) (hv_nonneg : ∀ n, 0 ≤ v n)
    (hu_pos : ∀ n, n ≠ 0 → 0 < u n)
    {k : ℕ} (hk : k ≠ 0)
    (lambda1 lambda2 : ℝ)
    (hlambda1 : 0 ≤ lambda1)
    (hlambda2 : 0 ≤ lambda2) (hlambda2_lt : lambda2 < 2)
    (majorant : ℕ → ℝ) (hmajorant : ∀ i, 0 ≤ majorant i)
    (hlocal : ∀ (p : ℕ), p.Prime → ∀ i j : ℕ,
      u (p ^ (i + j)) * v (p ^ j) ≤ majorant i * lambda2 ^ j)
    (hpow : ∀ (p : ℕ), p.Prime → ∀ j : ℕ,
      u (p ^ (k.factorization p + (j + 1))) * v (p ^ (j + 1)) /
          u (p ^ (k.factorization p)) ≤
        lambda1 * lambda2 ^ j)
    (N : ℕ) (hN : 2 ≤ N) :
    shiftedConvolutionSum u v k N ≤
      (HalberstamScratch.explicitMassConstant lambda1 lambda2 + 1) *
        (N : ℝ) / Real.log (N : ℝ) *
          correctedInfiniteEulerProduct u v k N *
            largePrimeShiftProduct u k N := by
  apply multiplicative_convolution_mean_value_II
    u v hu hv hu_one hv_one hu_nonneg hv_nonneg hu_pos hk
    lambda1 lambda2 hlambda1 hlambda2 hlambda2_lt hpow N hN
  · intro p hpP
    have hp := Nat.prime_of_mem_primesBelow hpP
    simpa [Nat.zero_add] using
      (localSeries_summable_of_prime_power_geometric
        u v hp 0 (majorant 0) lambda2 (hmajorant 0) hlambda2 hlambda2_lt
        (fun j => mul_nonneg (hu_nonneg _) (hv_nonneg _))
        (fun j => hlocal p hp 0 j)).1
  · intro p hpP
    have hp := Nat.prime_of_mem_primeFactors (Finset.mem_inter.mp hpP).1
    exact (localSeries_summable_of_prime_power_geometric
      u v hp (k.factorization p) (majorant (k.factorization p)) lambda2
      (hmajorant _) hlambda2 hlambda2_lt
      (fun j => mul_nonneg (hu_nonneg _) (hv_nonneg _))
      (fun j => hlocal p hp (k.factorization p) j)).1
  · intro p hpP
    have hp := Nat.prime_of_mem_primeFactors (Finset.mem_inter.mp hpP).1
    exact (localSeries_summable_of_prime_power_geometric
      u v hp (k.factorization p) (majorant (k.factorization p)) lambda2
      (hmajorant _) hlambda2 hlambda2_lt
      (fun j => mul_nonneg (hu_nonneg _) (hv_nonneg _))
      (fun j => hlocal p hp (k.factorization p) j)).2

end ErdosTenenbaumLemma2Scratch

#print axioms ErdosTenenbaumLemma2Scratch.product_replace_on_subset
#print axioms ErdosTenenbaumLemma2Scratch.multiplicative_convolution_mean_value_II_of_basic_engine
#print axioms ErdosTenenbaumLemma2Scratch.multiplicative_convolution_mean_value_II_infinite_of_basic_engine
#print axioms ErdosTenenbaumLemma2Scratch.raw_multiplicative_convolution_engine
#print axioms ErdosTenenbaumLemma2Scratch.multiplicative_convolution_mean_value_II
#print axioms ErdosTenenbaumLemma2Scratch.multiplicative_convolution_mean_value_II_of_geometric_majorants
