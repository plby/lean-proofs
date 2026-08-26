import ErdosProblems.Erdos67.StationaryEntropy
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Data.ZMod.Basic

/-!
# Finite concentration for the stationary entropy argument

The bounded-variable exponential estimate is proved directly by convexity and
the elementary bound on `cosh`. No asymptotic probability theorem is needed.
-/

open scoped BigOperators
open Finset

namespace Erdos67.FiniteEntropy

variable {α : Type*} [Fintype α]

theorem exp_le_endpoint_interpolation {A x : ℝ} (hA : 0 < A) (hx : |x| ≤ A) (t : ℝ) :
    Real.exp (t * x) ≤ (A - x) / (2 * A) * Real.exp (-t * A) +
      (A + x) / (2 * A) * Real.exp (t * A) := by
  have hleft : 0 ≤ (A - x) / (2 * A) :=
    div_nonneg (sub_nonneg.mpr (abs_le.mp hx).2) (by positivity)
  have hright : 0 ≤ (A + x) / (2 * A) :=
    div_nonneg (by linarith [(abs_le.mp hx).1]) (by positivity)
  have hsum : (A - x) / (2 * A) + (A + x) / (2 * A) = 1 := by
    field_simp
    ring
  have h := convexOn_exp.2 (Set.mem_univ (-t * A)) (Set.mem_univ (t * A))
    hleft hright hsum
  have harg : (A - x) / (2 * A) * (-t * A) + (A + x) / (2 * A) * (t * A) =
      t * x := by
    field_simp
    ring
  simpa only [smul_eq_mul, harg] using h

/-- Hoeffding's exponential estimate for a centered finite variable in `[-A,A]`. -/
theorem finite_centered_mgf_le (p : FinProb α) (X : α → ℝ) {A : ℝ}
    (hA : 0 ≤ A) (hX : ∀ a, |X a| ≤ A) (hmean : (∑ a, p a * X a) = 0) (t : ℝ) :
    (∑ a, p a * Real.exp (t * X a)) ≤ Real.exp (A ^ 2 * t ^ 2 / 2) := by
  rcases hA.eq_or_lt with hA | hA
  · have hzero : ∀ a, X a = 0 := by
      intro a
      apply abs_eq_zero.mp
      exact le_antisymm (by simpa only [← hA] using hX a) (abs_nonneg _)
    simp only [hzero, mul_zero, Real.exp_zero, mul_one, stdSimplex.sum_eq_one,
      ← hA, zero_pow (by omega : 2 ≠ 0), zero_mul, zero_div, le_refl]
  · have hweighted_left : (∑ a, p a * ((A - X a) / (2 * A))) = 1 / 2 := by
      simp_rw [← mul_div_assoc, mul_sub]
      rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.sum_mul,
        stdSimplex.sum_eq_one, one_mul, hmean, sub_zero]
      field_simp
    have hweighted_right : (∑ a, p a * ((A + X a) / (2 * A))) = 1 / 2 := by
      simp_rw [← mul_div_assoc, mul_add]
      rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.sum_mul,
        stdSimplex.sum_eq_one, one_mul, hmean, add_zero]
      field_simp
    calc
      (∑ a, p a * Real.exp (t * X a)) ≤
          ∑ a, p a * ((A - X a) / (2 * A) * Real.exp (-t * A) +
            (A + X a) / (2 * A) * Real.exp (t * A)) :=
        Finset.sum_le_sum fun a _ ↦ mul_le_mul_of_nonneg_left
          (exp_le_endpoint_interpolation hA (hX a) t) (prob_nonneg p a)
      _ = Real.cosh (t * A) := by
        simp_rw [mul_add, Finset.sum_add_distrib, ← mul_assoc, ← Finset.sum_mul]
        rw [hweighted_left, hweighted_right, Real.cosh_eq]
        simp only [neg_mul]
        ring
      _ ≤ Real.exp ((t * A) ^ 2 / 2) := Real.cosh_le_exp_half_sq _
      _ = Real.exp (A ^ 2 * t ^ 2 / 2) := by congr 1; ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*} [∀ i, Fintype (A i)]

/-- Product of a finite family of finite probability vectors. -/
noncomputable def piVector (p : ∀ i, FinProb (A i)) : FinProb (∀ i, A i) :=
  ⟨fun y ↦ ∏ i, p i (y i), by
    constructor
    · intro y
      exact Finset.prod_nonneg fun i _ ↦ prob_nonneg (p i) (y i)
    · rw [← Fintype.prod_sum]
      simp only [stdSimplex.sum_eq_one, Finset.prod_const_one]⟩

theorem piVector_expectation_prod (p : ∀ i, FinProb (A i)) (F : ∀ i, A i → ℝ) :
    (∑ y, piVector p y * ∏ i, F i (y i)) = ∏ i, ∑ a, p i a * F i a := by
  change (∑ y : (∀ i, A i), (∏ i, p i (y i)) * ∏ i, F i (y i)) = _
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a ↦ p i a * F i a)).symm

theorem piVector_mgf_sum (p : ∀ i, FinProb (A i)) (F : ∀ i, A i → ℝ) (t : ℝ) :
    (∑ y, piVector p y * Real.exp (t * ∑ i, F i (y i))) =
      ∏ i, ∑ a, p i a * Real.exp (t * F i a) := by
  simp_rw [Finset.mul_sum, Real.exp_sum]
  exact piVector_expectation_prod p (fun i a ↦ Real.exp (t * F i a))

theorem piVector_mgf_sum_le (p : ∀ i, FinProb (A i)) (F : ∀ i, A i → ℝ)
    (K : ι → ℝ) (t : ℝ)
    (hF : ∀ i, (∑ a, p i a * Real.exp (t * F i a)) ≤ Real.exp (K i)) :
    (∑ y, piVector p y * Real.exp (t * ∑ i, F i (y i))) ≤
      Real.exp (∑ i, K i) := by
  rw [piVector_mgf_sum, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro i _
    exact (exponential_sum_pos (p i) _).le
  · intro i _
    exact hF i

theorem piVector_uniform [∀ i, Nonempty (A i)] :
    piVector (fun i ↦ uniformVector (α := A i)) = uniformVector (α := ∀ i, A i) := by
  apply Subtype.ext
  funext y
  change (∏ i, (Fintype.card (A i) : ℝ)⁻¹) = (Fintype.card (∀ i, A i) : ℝ)⁻¹
  simp only [Fintype.card_pi, Nat.cast_prod, Finset.prod_inv_distrib]

end Erdos67.FiniteEntropy

namespace Erdos67.StationaryConcentration

variable {ι β : Type*} [Fintype ι]

open scoped Classical in
/-- An injectively labelled fiber contains at most one coefficient. -/
theorem abs_sum_fiber_le_one (label : ι → β) (hinj : Function.Injective label)
    (a : ι → ℝ) (ha : ∀ i, |a i| ≤ 1) (b : β) :
    |∑ i, if label i = b then a i else 0| ≤ 1 := by
  classical
  by_cases hb : ∃ i, label i = b
  · obtain ⟨i, hi⟩ := hb
    have heq : (∑ j, if label j = b then a j else 0) = a i := by
      rw [Finset.sum_eq_single i]
      · simp only [hi, if_true]
      · intro j _ hji
        have hj : label j ≠ b := fun hj ↦ hji (hinj (hj.trans hi.symm))
        simp only [hj, if_false]
      · simp
    rw [heq]
    exact ha i
  · have heq : (∑ j, if label j = b then a j else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      simp only [show label i ≠ b from fun hi ↦ hb ⟨i, hi⟩, if_false]
    rw [heq, abs_zero]
    norm_num

theorem neg_succ_residue_injective {L p : ℕ} (hLp : L ≤ p) :
    Function.Injective (fun i : Fin L ↦ -((i.val : ZMod p) + 1)) := by
  intro i j hij
  have hcast : (i.val : ZMod p) = (j.val : ZMod p) := add_right_cancel (neg_injective hij)
  have hmod := (ZMod.natCast_eq_natCast_iff' i.val j.val p).mp hcast
  rw [Nat.mod_eq_of_lt (i.isLt.trans_le hLp), Nat.mod_eq_of_lt (j.isLt.trans_le hLp)] at hmod
  exact Fin.ext hmod

/-- A single centered residue observable in the block of moduli `[L,2L]`. -/
noncomputable def residueObservable (L p : ℕ) (a : Fin L → ℝ) (y : ZMod p) : ℝ :=
  ((p : ℝ) * (∑ i, if y = -((i.val : ZMod p) + 1) then a i else 0) - ∑ i, a i) / L

theorem abs_residueObservable_le_three {L p : ℕ} (hL : 0 < L)
    (hLp : L ≤ p) (hpL : p ≤ 2 * L) (a : Fin L → ℝ) (ha : ∀ i, |a i| ≤ 1)
    (y : ZMod p) : |residueObservable L p a y| ≤ 3 := by
  have hfiber : |∑ i, if y = -((i.val : ZMod p) + 1) then a i else 0| ≤ 1 := by
    simpa only [eq_comm] using abs_sum_fiber_le_one
      (fun i : Fin L ↦ -((i.val : ZMod p) + 1)) (neg_succ_residue_injective hLp) a ha y
  have hsum : |∑ i, a i| ≤ (L : ℝ) := by
    calc
      |∑ i, a i| ≤ ∑ i, |a i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : Fin L, (1 : ℝ) := Finset.sum_le_sum fun i _ ↦ ha i
      _ = L := by simp
  unfold residueObservable
  have hL' : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  rw [abs_div, abs_of_pos hL']
  apply (div_le_iff₀ hL').mpr
  have hmul : |(p : ℝ) * ∑ i, if y = -((i.val : ZMod p) + 1) then a i else 0| ≤ p := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg p)]
    exact (mul_le_mul_of_nonneg_left hfiber (Nat.cast_nonneg p)).trans_eq (mul_one _)
  have htriangle := abs_sub
    ((p : ℝ) * ∑ i, if y = -((i.val : ZMod p) + 1) then a i else 0) (∑ i, a i)
  have hpL' : (p : ℝ) ≤ 2 * L := by exact_mod_cast hpL
  linarith

theorem sum_residueObservable_eq_zero (L p : ℕ) [NeZero p] (a : Fin L → ℝ) :
    (∑ y : ZMod p, residueObservable L p a y) = 0 := by
  classical
  have hsum : (∑ y : ZMod p, ∑ i, if y = -((i.val : ZMod p) + 1) then a i else 0) =
      ∑ i, a i := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp
  simp only [residueObservable, ← Finset.sum_div, Finset.sum_sub_distrib,
    ← Finset.mul_sum, hsum, Finset.sum_const, Finset.card_univ,
    ZMod.card, nsmul_eq_mul, sub_self, zero_div]

theorem uniform_mean_residueObservable_eq_zero (L p : ℕ) [NeZero p] (a : Fin L → ℝ) :
    (∑ y : ZMod p, FiniteEntropy.uniformVector y * residueObservable L p a y) = 0 := by
  change (∑ y : ZMod p, (Fintype.card (ZMod p) : ℝ)⁻¹ *
    residueObservable L p a y) = 0
  rw [← Finset.mul_sum, sum_residueObservable_eq_zero, mul_zero]

/-- The exact exponential constant for one weighted residue observable. -/
theorem uniform_mgf_weighted_residueObservable_le {L p : ℕ} [NeZero p]
    (hL : 0 < L) (hLp : L ≤ p) (hpL : p ≤ 2 * L)
    (a : Fin L → ℝ) (ha : ∀ i, |a i| ≤ 1) (δ t : ℝ) :
    (∑ y : ZMod p, FiniteEntropy.uniformVector y *
      Real.exp (t * (δ * residueObservable L p a y))) ≤
        Real.exp ((9 / 2 : ℝ) * t ^ 2 * δ ^ 2) := by
  have hbound (y : ZMod p) : |δ * residueObservable L p a y| ≤ 3 * |δ| := by
    rw [abs_mul]
    have h := mul_le_mul_of_nonneg_left
      (abs_residueObservable_le_three hL hLp hpL a ha y) (abs_nonneg δ)
    simpa only [mul_comm] using h
  have hmean : (∑ y : ZMod p, FiniteEntropy.uniformVector y *
      (δ * residueObservable L p a y)) = 0 := by
    simp_rw [mul_left_comm (FiniteEntropy.uniformVector _) δ]
    rw [← Finset.mul_sum, uniform_mean_residueObservable_eq_zero, mul_zero]
  have h := FiniteEntropy.finite_centered_mgf_le FiniteEntropy.uniformVector
    (fun y ↦ δ * residueObservable L p a y) (by positivity : 0 ≤ 3 * |δ|)
    hbound hmean t
  have heq : (3 * |δ|) ^ 2 * t ^ 2 / 2 = (9 / 2 : ℝ) * t ^ 2 * δ ^ 2 := by
    rw [mul_pow, sq_abs]
    ring
  simpa only [heq] using h

/-- Independent residue coordinates give the exponential estimate for an entire
block. In the application the moduli are the primes in one dyadic interval. -/
theorem uniform_mgf_residue_block_le [DecidableEq ι] {L : ℕ}
    (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hL : 0 < L) (hLp : ∀ i, L ≤ p i) (hpL : ∀ i, p i ≤ 2 * L)
    (a : ι → Fin L → ℝ) (ha : ∀ i j, |a i j| ≤ 1) (δ : ι → ℝ) (t : ℝ) :
    (∑ y : (∀ i, ZMod (p i)), FiniteEntropy.uniformVector y *
      Real.exp (t * ∑ i, δ i * residueObservable L (p i) (a i) (y i))) ≤
        Real.exp ((9 / 2 : ℝ) * t ^ 2 * ∑ i, δ i ^ 2) := by
  have h := FiniteEntropy.piVector_mgf_sum_le
    (fun i ↦ FiniteEntropy.uniformVector (α := ZMod (p i)))
    (fun i y ↦ δ i * residueObservable L (p i) (a i) y)
    (fun i ↦ (9 / 2 : ℝ) * t ^ 2 * δ i ^ 2) t
    (fun i ↦ uniform_mgf_weighted_residueObservable_le hL (hLp i) (hpL i)
      (a i) (ha i) (δ i) t)
  simpa only [FiniteEntropy.piVector_uniform, ← Finset.mul_sum] using h

end Erdos67.StationaryConcentration
