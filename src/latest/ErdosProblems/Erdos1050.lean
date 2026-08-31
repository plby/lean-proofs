/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 1050.
https://www.erdosproblems.com/forum/thread/1050

Informal authors:
- Peter B. Borwein

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1050.md
-/
/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Lean Community
-/
import Mathlib
import ErdosProblems.Erdos250.Erdos250Core

/-!
# Erdős Problem 1050

We prove that
`∑' n : ℕ+, 1 / ((2 : ℝ) ^ (n : ℕ) - 3)` is irrational.

The proof is a contour-free specialization of Borwein's rational-function
construction for generalized Lambert series.  The detailed mathematical proof
and a map of the formal argument are in `tex/1050.tex`.
-/

open scoped BigOperators Topology

namespace Erdos1050

noncomputable section

open Polynomial

/-! ## The original series and a shifted Lambert series -/

/-- The `n`th term of the target series, with `n = 0` representing the
mathematical index `1`. -/
def targetTerm (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ (n + 1) - 3)

/-- The sum in Erdős Problem 1050, indexed by positive natural numbers. -/
def erdos1050Series : ℝ :=
  ∑' n : ℕ+, 1 / ((2 : ℝ) ^ (n : ℕ) - 3)

/-- A shifted generalized Lambert series. -/
def shiftedTerm (h : ℕ) : ℝ :=
  1 / (1 - (8 / 3 : ℝ) * 2 ^ (h + 1))

/-- The shifted value used in Borwein's construction. -/
def shiftedValue : ℝ :=
  ∑' h : ℕ, shiftedTerm h

lemma target_tail_nonneg (n : ℕ) : 0 ≤ targetTerm (n + 2) := by
  rw [targetTerm]
  have hx : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hpow : (2 : ℝ) ^ (n + 2 + 1) = 8 * 2 ^ n := by
    rw [show n + 2 + 1 = 3 + n by omega, pow_add]
    norm_num
  rw [hpow]
  exact one_div_nonneg.mpr (by nlinarith)

lemma target_tail_le (n : ℕ) :
    targetTerm (n + 2) ≤ (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ n := by
  have hx : 0 < (2 : ℝ) ^ n := by positivity
  have hx1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hden : 0 < 8 * (2 : ℝ) ^ n - 3 := by nlinarith
  rw [targetTerm]
  rw [show n + 2 + 1 = 3 + n by omega, pow_add]
  norm_num only [pow_succ, pow_zero, mul_one]
  rw [show (1 / 2 : ℝ) ^ n = 1 / (2 : ℝ) ^ n by
    simp]
  rw [div_le_iff₀ hden]
  field_simp
  nlinarith

lemma summable_target_nat : Summable targetTerm := by
  apply (summable_nat_add_iff 2).1
  apply Summable.of_nonneg_of_le target_tail_nonneg target_tail_le
  simpa [mul_assoc] using
    (summable_geometric_of_norm_lt_one (K := ℝ) (x := (1 / 2 : ℝ))
      (by norm_num)).mul_left (1 / 4 : ℝ)

lemma summable_target_pnat :
    Summable (fun n : ℕ+ => 1 / ((2 : ℝ) ^ (n : ℕ) - 3)) := by
  refine (summable_pnat_iff_summable_succ
    (f := fun n : ℕ => 1 / ((2 : ℝ) ^ n - 3))).2 ?_
  exact summable_target_nat.congr (fun n => by rfl)

lemma erdos1050Series_eq_tsum_target :
    erdos1050Series = ∑' n : ℕ, targetTerm n := by
  rw [erdos1050Series]
  simpa [targetTerm] using
    (tsum_pnat_eq_tsum_succ
      (f := fun n : ℕ => 1 / ((2 : ℝ) ^ n - 3)))

lemma shifted_eq_tail (h : ℕ) :
    shiftedTerm h = -3 * targetTerm (h + 3) := by
  have hp : (0 : ℝ) < 2 ^ h := by positivity
  have hone : (1 : ℝ) ≤ 2 ^ h := one_le_pow₀ (by norm_num)
  have hshift : (2 : ℝ) ^ (h + 1) = 2 ^ h * 2 := by rw [pow_succ]
  have htail : (2 : ℝ) ^ (h + 3 + 1) = 16 * 2 ^ h := by
    rw [show h + 3 + 1 = 4 + h by omega, pow_add]
    norm_num
  rw [shiftedTerm, targetTerm, hshift, htail]
  have h₁ : 1 - (8 / 3 : ℝ) * (2 ^ h * 2) ≠ 0 := by nlinarith
  have h₂ : 16 * (2 : ℝ) ^ h - 3 ≠ 0 := by nlinarith
  field_simp [h₁, h₂]
  have hden : 3 - 8 * (2 : ℝ) ^ h * 2 = -(2 ^ h * 16 - 3) := by ring
  exact calc
    1 / (3 - 8 * (2 : ℝ) ^ h * 2) = 1 / (-(2 ^ h * 16 - 3)) :=
      congrArg (fun x : ℝ => 1 / x) hden
    _ = -(1 / (2 ^ h * 16 - 3)) := by simp only [one_div, inv_neg]

lemma summable_shifted : Summable shiftedTerm := by
  have ht : Summable (fun h : ℕ => targetTerm (h + 3)) :=
    (summable_nat_add_iff 3).2 summable_target_nat
  exact (ht.mul_left (-3)).congr (fun h => (shifted_eq_tail h).symm)

lemma erdos1050Series_eq_one_fifth_sub_shifted :
    erdos1050Series = 1 / 5 - shiftedValue / 3 := by
  rw [erdos1050Series_eq_tsum_target, shiftedValue]
  have hsplit := summable_target_nat.sum_add_tsum_nat_add 3
  have htail : (∑' h : ℕ, targetTerm (h + 3)) = - (∑' h, shiftedTerm h) / 3 := by
    rw [show (∑' h, shiftedTerm h) = -3 * (∑' h : ℕ, targetTerm (h + 3)) by
      rw [← tsum_mul_left]
      exact tsum_congr shifted_eq_tail]
    ring
  rw [htail] at hsplit
  norm_num [targetTerm] at hsplit ⊢
  linarith

/-! ## Borwein's rational-function kernel -/

/-- Borwein's fixed parameter `8/3`, over the rationals. -/
def cRat : ℚ := 8 / 3

/-- The polynomial `-∏_{j=1}^{n-1} (X - 2^j)`. -/
def numeratorPoly (n : ℕ) : ℚ[X] :=
  -∏ j ∈ Finset.range (n - 1),
    (Polynomial.X - Polynomial.C ((2 : ℚ) ^ (j + 1)))

/-- The polynomial `∏_{k=1}^n (1 - (8/3) 2^k X)`. -/
def denominatorPoly (n : ℕ) : ℚ[X] :=
  ∏ k ∈ Finset.range n,
    (1 - Polynomial.C (cRat * (2 : ℚ) ^ (k + 1)) * Polynomial.X)

/-- The coefficients of the polynomial principal part at zero. -/
def principalCoeff (n r : ℕ) : ℚ :=
  Nat.strongRecOn r fun r ih =>
    (numeratorPoly n).coeff r -
      ∑ i ∈ (Finset.Icc 1 r).attach,
        (denominatorPoly n).coeff i * ih (r - i) (by
          have hi := i.property
          simp only [Finset.mem_Icc] at hi
          omega)

lemma principalCoeff_eq (n r : ℕ) :
    principalCoeff n r = (numeratorPoly n).coeff r -
      ∑ i ∈ Finset.Icc 1 r,
        (denominatorPoly n).coeff i * principalCoeff n (r - i) := by
  rw [principalCoeff, Nat.strongRecOn_eq]
  apply congrArg (fun x : ℚ => (numeratorPoly n).coeff r - x)
  change (∑ i ∈ (Finset.Icc 1 r).attach,
      (denominatorPoly n).coeff i * principalCoeff n (r - i)) = _
  exact Finset.sum_attach (Finset.Icc 1 r)
    (fun i : ℕ => (denominatorPoly n).coeff i * principalCoeff n (r - i))

/-- The polynomial part `Q_n` in the partial-fraction construction. -/
def principalPoly (n : ℕ) : ℚ[X] :=
  ∑ r ∈ Finset.range (n - 1),
    Polynomial.monomial r (principalCoeff n r)

lemma principalPoly_coeff (n r : ℕ) (hr : r < n - 1) :
    (principalPoly n).coeff r = principalCoeff n r := by
  classical
  simp [principalPoly, Polynomial.coeff_monomial, hr]

@[simp] lemma denominatorPoly_coeff_zero (n : ℕ) :
    (denominatorPoly n).coeff 0 = 1 := by
  rw [Polynomial.coeff_zero_eq_eval_zero, denominatorPoly, Polynomial.eval_prod]
  simp

lemma principal_mul_denominator_coeff (n r : ℕ) (hr : r < n - 1) :
    (principalPoly n * denominatorPoly n).coeff r =
      (numeratorPoly n).coeff r := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Finset.sum_range_succ]
  simp only [Nat.sub_self, denominatorPoly_coeff_zero, mul_one]
  rw [principalPoly_coeff n r hr, principalCoeff_eq]
  have hsum :
      (∑ x ∈ Finset.range r,
        (principalPoly n).coeff x * (denominatorPoly n).coeff (r - x)) =
      ∑ i ∈ Finset.Icc 1 r,
        (denominatorPoly n).coeff i * principalCoeff n (r - i) := by
    refine Finset.sum_bij'
      (fun x _ => r - x) (fun i _ => r - i) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_range] at hx
      simp only [Finset.mem_Icc]
      omega
    · intro i hi
      simp only [Finset.mem_Icc] at hi
      simp only [Finset.mem_range]
      omega
    · intro x hx
      simp only [Finset.mem_range] at hx
      omega
    · intro i hi
      simp only [Finset.mem_Icc] at hi
      omega
    · intro x hx
      simp only [Finset.mem_range] at hx
      rw [principalPoly_coeff]
      · have hrr : r - (r - x) = x := by omega
        rw [hrr]
        ring
      · omega
  rw [hsum]
  ring

lemma numeratorPoly_natDegree_lt (n : ℕ) (hn : 1 ≤ n) :
    (numeratorPoly n).natDegree < n := by
  rw [numeratorPoly]
  have h := Polynomial.natDegree_prod_le
    (s := Finset.range (n - 1))
    (f := fun j => Polynomial.X - Polynomial.C ((2 : ℚ) ^ (j + 1)))
  simp only [Polynomial.natDegree_neg]
  calc
    (∏ j ∈ Finset.range (n - 1),
        (Polynomial.X - Polynomial.C ((2 : ℚ) ^ (j + 1)))).natDegree
        ≤ ∑ j ∈ Finset.range (n - 1),
            (Polynomial.X - Polynomial.C ((2 : ℚ) ^ (j + 1))).natDegree := h
    _ = ∑ _j ∈ Finset.range (n - 1), 1 := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Polynomial.natDegree_X_sub_C]
    _ = n - 1 := by simp
    _ < n := by omega

lemma denominatorPoly_natDegree_le (n : ℕ) :
    (denominatorPoly n).natDegree ≤ n := by
  rw [denominatorPoly]
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  calc
    (∑ k ∈ Finset.range n,
        (1 - Polynomial.C (cRat * (2 : ℚ) ^ (k + 1)) * Polynomial.X).natDegree)
        ≤ ∑ _k ∈ Finset.range n, 1 := by
          apply Finset.sum_le_sum
          intro k hk
          have hc :
              (Polynomial.C (cRat * (2 : ℚ) ^ (k + 1))).natDegree ≤ 0 := by
            rw [Polynomial.natDegree_C]
          have hx : (Polynomial.X : ℚ[X]).natDegree ≤ 1 := by simp
          have hcx :
              (Polynomial.C (cRat * (2 : ℚ) ^ (k + 1)) *
                Polynomial.X).natDegree ≤ 1 :=
            Polynomial.natDegree_mul_le.trans (Nat.add_le_add hc hx)
          exact (Polynomial.natDegree_sub_le (1 : ℚ[X])
            (Polynomial.C (cRat * (2 : ℚ) ^ (k + 1)) * Polynomial.X)).trans
            (max_le (by simp) hcx)
    _ = n := by simp

lemma principalPoly_natDegree_lt (n : ℕ) (hn : 2 ≤ n) :
    (principalPoly n).natDegree < n - 1 := by
  rw [principalPoly]
  refine lt_of_le_of_lt
    (Polynomial.natDegree_sum_le_of_forall_le (Finset.range (n - 1))
      (n := n - 2) (fun r => Polynomial.monomial r (principalCoeff n r)) ?_) ?_
  · intro r hr
    simp only [Finset.mem_range] at hr
    exact (Polynomial.natDegree_monomial_le (principalCoeff n r)).trans (by omega)
  · omega

/-- The numerator left after removing the principal part at zero. -/
def remainderPoly (n : ℕ) : ℚ[X] :=
  numeratorPoly n - principalPoly n * denominatorPoly n

lemma remainderPoly_coeff_zero (n r : ℕ) (hr : r < n - 1) :
    (remainderPoly n).coeff r = 0 := by
  rw [remainderPoly, Polynomial.coeff_sub, principal_mul_denominator_coeff n r hr]
  exact sub_self _

lemma remainderPoly_X_pow_dvd (n : ℕ) :
    Polynomial.X ^ (n - 1) ∣ remainderPoly n := by
  exact Polynomial.X_pow_dvd_iff.mpr (remainderPoly_coeff_zero n)

lemma remainderPoly_natDegree_lt (n : ℕ) (hn : 2 ≤ n) :
    (remainderPoly n).natDegree < (n - 1) + n := by
  rw [remainderPoly]
  refine (Polynomial.natDegree_sub_le _ _).trans_lt ?_
  apply max_lt
  · exact (numeratorPoly_natDegree_lt n (by omega)).trans_le (by omega)
  · refine lt_of_le_of_lt Polynomial.natDegree_mul_le ?_
    exact Nat.add_lt_add_of_lt_of_le (principalPoly_natDegree_lt n hn)
      (denominatorPoly_natDegree_le n)

/-- The polynomial remaining after division by the zero of order `n-1`. -/
def residualPoly (N : ℕ) : ℚ[X] :=
  Classical.choose (remainderPoly_X_pow_dvd (N + 2))

lemma residualPoly_spec (N : ℕ) :
    remainderPoly (N + 2) = Polynomial.X ^ (N + 1) * residualPoly N := by
  exact Classical.choose_spec (remainderPoly_X_pow_dvd (N + 2))

lemma residualPoly_natDegree_lt (N : ℕ) :
    (residualPoly N).natDegree < N + 2 := by
  by_cases hzero : residualPoly N = 0
  · simp [hzero]
  have hdeg := remainderPoly_natDegree_lt (N + 2) (by omega)
  rw [residualPoly_spec N, Polynomial.natDegree_X_pow_mul (N + 1) hzero] at hdeg
  omega

/-! The simple poles of the remaining rational function. -/

/-- The `k`th pole, with `k = 0` representing the mathematical index `1`. -/
def pole (k : ℕ) : ℚ :=
  1 / (cRat * (2 : ℚ) ^ (k + 1))

/-- The denominator factor vanishing at `pole k`. -/
def poleFactor (k : ℕ) : ℚ[X] :=
  1 - Polynomial.C (cRat * (2 : ℚ) ^ (k + 1)) * Polynomial.X

/-- The product of all denominator factors except the `k`th. -/
def poleRest (n k : ℕ) : ℚ[X] :=
  ∏ l ∈ (Finset.range n).erase k, poleFactor l

/-- The coefficient at a simple pole. -/
def poleCoeff (N k : ℕ) : ℚ :=
  (residualPoly N).eval (pole k) / (poleRest (N + 2) k).eval (pole k)

/-- The polynomial reconstructed from the values at all simple poles. -/
def simplePolePoly (N : ℕ) : ℚ[X] :=
  ∑ k ∈ Finset.range (N + 2),
    Polynomial.C (poleCoeff N k) * poleRest (N + 2) k

@[simp] lemma poleFactor_eval (k : ℕ) :
    (poleFactor k).eval (pole k) = 0 := by
  rw [poleFactor, pole]
  simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  field_simp [cRat]
  ring

lemma pole_injective : Function.Injective pole := by
  intro i j hij
  have halpha : cRat * (2 : ℚ) ^ (i + 1) = cRat * (2 : ℚ) ^ (j + 1) := by
    apply inv_injective
    simpa [pole, one_div] using hij
  have hp : (2 : ℚ) ^ (i + 1) = (2 : ℚ) ^ (j + 1) := by
    exact mul_left_cancel₀ (by norm_num [cRat] : cRat ≠ 0) halpha
  have hij' : i + 1 = j + 1 :=
    (pow_right_strictMono₀ (by norm_num : (1 : ℚ) < 2)).injective hp
  omega

lemma poleRest_eval_ne_zero {n k : ℕ} :
    (poleRest n k).eval (pole k) ≠ 0 := by
  rw [poleRest, Polynomial.eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro l hl
  have hlk : l ≠ k := Finset.ne_of_mem_erase hl
  have hne : pole k ≠ pole l := fun h => hlk ((pole_injective h).symm)
  simp only [poleFactor, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  rw [sub_ne_zero]
  intro h
  have hnonzero : cRat * (2 : ℚ) ^ (l + 1) ≠ 0 := by
    exact mul_ne_zero (by norm_num [cRat]) (pow_ne_zero _ (by norm_num))
  apply hne
  have hkform : pole k = 1 / (cRat * (2 : ℚ) ^ (l + 1)) :=
    (eq_div_iff hnonzero).2 (by simpa [mul_comm] using h.symm)
  simpa only [pole] using hkform

lemma poleRest_eval_eq_zero {n i k : ℕ} (hi : i ∈ Finset.range n) (hik : i ≠ k) :
    (poleRest n k).eval (pole i) = 0 := by
  rw [poleRest, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hik, hi⟩)
  exact poleFactor_eval i

lemma simplePolePoly_eval (N : ℕ) {i : ℕ} (hi : i < N + 2) :
    (simplePolePoly N).eval (pole i) = (residualPoly N).eval (pole i) := by
  rw [simplePolePoly, Polynomial.eval_finsetSum]
  rw [Finset.sum_eq_single i]
  · simp only [Polynomial.eval_mul, Polynomial.eval_C]
    rw [poleCoeff, div_mul_cancel₀]
    exact poleRest_eval_ne_zero
  · intro k hk hki
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    rw [poleRest_eval_eq_zero (Finset.mem_range.mpr hi) hki.symm, mul_zero]
  · exact fun h => (h (Finset.mem_range.mpr hi)).elim

lemma poleRest_natDegree_le (n k : ℕ) (hk : k ∈ Finset.range n) :
    (poleRest n k).natDegree ≤ n - 1 := by
  rw [poleRest]
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  calc
    (∑ l ∈ (Finset.range n).erase k, (poleFactor l).natDegree)
        ≤ ∑ _l ∈ (Finset.range n).erase k, 1 := by
          apply Finset.sum_le_sum
          intro l hl
          unfold poleFactor
          refine (Polynomial.natDegree_sub_le _ _).trans (max_le (by simp) ?_)
          simpa only [pow_one] using
            Polynomial.natDegree_C_mul_X_pow_le
              (cRat * (2 : ℚ) ^ (l + 1)) 1
    _ = n - 1 := by simp [Finset.card_erase_of_mem hk]

lemma simplePolePoly_natDegree_lt (N : ℕ) :
    (simplePolePoly N).natDegree < N + 2 := by
  rw [simplePolePoly]
  have hdegree :
      (∑ k ∈ Finset.range (N + 2),
        Polynomial.C (poleCoeff N k) * poleRest (N + 2) k).natDegree ≤ N + 1 := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro k hk
    have hrest : (poleRest (N + 2) k).natDegree ≤ N + 1 := by
      have hrest' := poleRest_natDegree_le (N + 2) k hk
      omega
    exact (Polynomial.natDegree_C_mul_le _ _).trans hrest
  exact hdegree.trans_lt (by omega)

lemma residualPoly_eq_simplePolePoly (N : ℕ) :
    residualPoly N = simplePolePoly N := by
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq
      (f := fun i : Fin (N + 2) => pole i)
  · exact pole_injective.comp Fin.val_injective
  · intro i
    exact (simplePolePoly_eval N i.isLt).symm
  · simp only [Fintype.card_fin]
    exact max_lt (residualPoly_natDegree_lt N) (simplePolePoly_natDegree_lt N)

/-! ## Integer coefficients after clearing powers of three -/

/-- A rational number is integral if it is the cast of an integer. -/
def RatIntegral (x : ℚ) : Prop := ∃ z : ℤ, x = (z : ℚ)

namespace RatIntegral

lemma intCast (z : ℤ) : RatIntegral (z : ℚ) := ⟨z, rfl⟩

lemma add {x y : ℚ} (hx : RatIntegral x) (hy : RatIntegral y) :
    RatIntegral (x + y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a + b, by push_cast; rfl⟩

lemma sub {x y : ℚ} (hx : RatIntegral x) (hy : RatIntegral y) :
    RatIntegral (x - y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a - b, by push_cast; rfl⟩

lemma mul {x y : ℚ} (hx : RatIntegral x) (hy : RatIntegral y) :
    RatIntegral (x * y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a * b, by push_cast; rfl⟩

lemma sum {s : Finset ι} {f : ι → ℚ} (hf : ∀ i ∈ s, RatIntegral (f i)) :
    RatIntegral (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact intCast 0
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hf a (by simp)).add (ih fun i hi => hf i (by simp [hi]))

end RatIntegral

lemma denominatorPoly_succ (n : ℕ) :
    denominatorPoly (n + 1) = denominatorPoly n *
      (1 - Polynomial.C (cRat * (2 : ℚ) ^ (n + 1)) * Polynomial.X) := by
  rw [denominatorPoly, denominatorPoly, Finset.prod_range_succ]

lemma denominatorPoly_coeff_succ_zero (n : ℕ) :
    (denominatorPoly (n + 1)).coeff 0 = (denominatorPoly n).coeff 0 := by
  rw [denominatorPoly_succ]
  simp

lemma denominatorPoly_coeff_succ_succ (n r : ℕ) :
    (denominatorPoly (n + 1)).coeff (r + 1) =
      (denominatorPoly n).coeff (r + 1) -
        (cRat * (2 : ℚ) ^ (n + 1)) * (denominatorPoly n).coeff r := by
  rw [denominatorPoly_succ, mul_sub, mul_one]
  rw [Polynomial.coeff_sub, ← mul_assoc, Polynomial.coeff_mul_X,
    Polynomial.coeff_mul_C]
  ring

lemma denominatorPoly_coeff_scaled_integral : ∀ n r : ℕ,
    RatIntegral ((3 : ℚ) ^ r * (denominatorPoly n).coeff r) := by
  intro n
  induction n with
  | zero =>
      intro r
      cases r with
      | zero =>
          refine ⟨1, ?_⟩
          simp [denominatorPoly]
      | succ r =>
          refine ⟨0, ?_⟩
          simp only [denominatorPoly, Finset.prod_range_zero]
          rw [Polynomial.coeff_one]
          simp
  | succ n ih =>
      intro r
      cases r with
      | zero =>
          simpa [denominatorPoly_coeff_succ_zero] using ih 0
      | succ r =>
          rw [denominatorPoly_coeff_succ_succ]
          have h1 := ih (r + 1)
          have h2 := ih r
          have hc : RatIntegral
              (((8 * 2 ^ (n + 1) : ℤ) : ℚ) *
                ((3 : ℚ) ^ r * (denominatorPoly n).coeff r)) :=
            (RatIntegral.intCast (8 * 2 ^ (n + 1))).mul h2
          have hsub := h1.sub hc
          convert hsub using 1
          rw [cRat]
          push_cast
          ring

/-- The integer polynomial whose rational image is `numeratorPoly`. -/
def numeratorPolyInt (n : ℕ) : ℤ[X] :=
  -∏ j ∈ Finset.range (n - 1),
    (Polynomial.X - Polynomial.C ((2 : ℤ) ^ (j + 1)))

lemma numeratorPoly_eq_map (n : ℕ) :
    numeratorPoly n = (numeratorPolyInt n).map (Int.castRingHom ℚ) := by
  rw [numeratorPoly, numeratorPolyInt, Polynomial.map_neg, Polynomial.map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  congr 2
  norm_cast

lemma numeratorPoly_coeff_integral (n r : ℕ) :
    RatIntegral ((numeratorPoly n).coeff r) := by
  refine ⟨(numeratorPolyInt n).coeff r, ?_⟩
  rw [numeratorPoly_eq_map, Polynomial.coeff_map]
  rfl

lemma principalCoeff_scaled_integral (n r : ℕ) :
    RatIntegral ((3 : ℚ) ^ r * principalCoeff n r) := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
      rw [principalCoeff_eq, mul_sub, Finset.mul_sum]
      have hnum : RatIntegral ((3 : ℚ) ^ r * (numeratorPoly n).coeff r) :=
        by simpa using
          (RatIntegral.intCast (3 ^ r)).mul (numeratorPoly_coeff_integral n r)
      have hsum : RatIntegral
          (∑ i ∈ Finset.Icc 1 r,
            (3 : ℚ) ^ r *
              ((denominatorPoly n).coeff i * principalCoeff n (r - i))) := by
        apply RatIntegral.sum
        intro i hi
        have hir : i ≤ r := (Finset.mem_Icc.mp hi).2
        have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
        have hd := denominatorPoly_coeff_scaled_integral n i
        have hp := ih (r - i) (by omega)
        have hmul := hd.mul hp
        convert hmul using 1
        have hpow : (3 : ℚ) ^ r = 3 ^ i * 3 ^ (r - i) := by
          rw [← pow_add, Nat.add_sub_of_le hir]
        rw [hpow]
        ring
      exact hnum.sub hsum

/-! ## Explicit pole coefficients and their common denominator -/

lemma denominatorPoly_eq_factor_mul_rest {n k : ℕ} (hk : k ∈ Finset.range n) :
    denominatorPoly n = poleFactor k * poleRest n k := by
  simp only [denominatorPoly, poleRest, poleFactor]
  exact (Finset.mul_prod_erase (Finset.range n)
    (fun l => 1 - Polynomial.C (cRat * (2 : ℚ) ^ (l + 1)) * Polynomial.X) hk).symm

lemma denominatorPoly_eval_pole {n k : ℕ} (hk : k ∈ Finset.range n) :
    (denominatorPoly n).eval (pole k) = 0 := by
  rw [denominatorPoly_eq_factor_mul_rest hk, Polynomial.eval_mul, poleFactor_eval, zero_mul]

lemma residualPoly_eval_pole (N : ℕ) {k : ℕ} (hk : k < N + 2) :
    (pole k) ^ (N + 1) * (residualPoly N).eval (pole k) =
      (numeratorPoly (N + 2)).eval (pole k) := by
  have h := congrArg (Polynomial.eval (pole k)) (residualPoly_spec N)
  simp only [remainderPoly, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X,
    denominatorPoly_eval_pole (Finset.mem_range.mpr hk), mul_zero, sub_zero] at h
  exact h.symm

lemma pole_ne_zero (k : ℕ) : pole k ≠ 0 := by
  simp [pole, cRat]

lemma poleCoeff_eq_eval_div (N : ℕ) {k : ℕ} (hk : k < N + 2) :
    poleCoeff N k =
      (numeratorPoly (N + 2)).eval (pole k) /
        ((pole k) ^ (N + 1) * (poleRest (N + 2) k).eval (pole k)) := by
  rw [poleCoeff]
  field_simp [poleRest_eval_ne_zero, pole_ne_zero]
  simpa [mul_comm] using residualPoly_eval_pole N hk

/-- `∏_{r=1}^s (2^r-1)`. -/
def oddProduct (s : ℕ) : ℕ :=
  ∏ r ∈ Finset.range s, (2 ^ (r + 1) - 1)

lemma oddProduct_succ (s : ℕ) :
    oddProduct (s + 1) = oddProduct s * (2 ^ (s + 1) - 1) := by
  simp [oddProduct, Finset.prod_range_succ]

lemma oddProduct_dvd_of_le {a b : ℕ} (hab : a ≤ b) : oddProduct a ∣ oddProduct b := by
  induction b with
  | zero => simp_all
  | succ b ih =>
      rw [oddProduct_succ]
      by_cases h : a ≤ b
      · exact dvd_mul_of_dvd_left (ih h) _
      · have ha : a = b + 1 := by omega
        simp [ha, oddProduct_succ]

/-- The extra lower-half product used to clear the two overlapping odd
denominators in every pole coefficient. -/
def overlapIndex (n : ℕ) : ℕ := (n - 1) / 2

/-- The odd common denominator for all simple-pole coefficients of order `n`. -/
def oddCommon (n : ℕ) : ℕ :=
  oddProduct (n - 1) * oddProduct (overlapIndex n)

lemma min_side_le_overlap {n k : ℕ} (hk : k < n) :
    min k (n - 1 - k) ≤ overlapIndex n := by
  rw [overlapIndex]
  omega

lemma pole_odd_denominator_dvd {n k : ℕ} (hk : k < n) :
    oddProduct k * oddProduct (n - 1 - k) ∣ oddCommon n := by
  by_cases hle : k ≤ n - 1 - k
  · have hkover : oddProduct k ∣ oddProduct (overlapIndex n) :=
      oddProduct_dvd_of_le (by
        simpa [min_eq_left hle] using min_side_le_overlap hk)
    have hside : oddProduct (n - 1 - k) ∣ oddProduct (n - 1) :=
      oddProduct_dvd_of_le (by omega)
    have hmul := mul_dvd_mul hkover hside
    simpa [oddCommon, mul_comm] using hmul
  · have hrev : n - 1 - k ≤ k := by omega
    have hkmain : oddProduct k ∣ oddProduct (n - 1) :=
      oddProduct_dvd_of_le (by omega)
    have hside : oddProduct (n - 1 - k) ∣ oddProduct (overlapIndex n) :=
      oddProduct_dvd_of_le (by
        simpa [min_eq_right hrev] using min_side_le_overlap hk)
    simpa [oddCommon] using mul_dvd_mul hkmain hside

lemma numerator_eval_div_pow (n k : ℕ) :
    (numeratorPoly n).eval (pole k) / (pole k) ^ (n - 1) =
      -∏ j ∈ Finset.range (n - 1),
        (1 - (2 : ℚ) ^ (j + 1) / pole k) := by
  rw [numeratorPoly, Polynomial.eval_neg, Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, neg_div]
  congr 1
  rw [show (pole k) ^ (n - 1) =
      ∏ _j ∈ Finset.range (n - 1), pole k by simp]
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  field_simp [pole_ne_zero]

/-- The integer numerator obtained after multiplying the dimensionless
numerator at a pole by `3^(n-1)`. -/
def scaledNumeratorInt (n k : ℕ) : ℤ :=
  -∏ j ∈ Finset.range (n - 1),
    (3 - 8 * 2 ^ (j + k + 2) : ℤ)

lemma scaled_numerator_eq_intCast (n k : ℕ) :
    (3 : ℚ) ^ (n - 1) *
        ((numeratorPoly n).eval (pole k) / (pole k) ^ (n - 1)) =
      (scaledNumeratorInt n k : ℚ) := by
  rw [numerator_eval_div_pow, scaledNumeratorInt]
  push_cast
  simp only [mul_neg, neg_inj]
  rw [show (3 : ℚ) ^ (n - 1) = ∏ _j ∈ Finset.range (n - 1), (3 : ℚ) by simp]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  rw [pole]
  rw [show j + k + 2 = (j + 1) + (k + 1) by omega, pow_add]
  field_simp [cRat]
  norm_num [cRat]
  ring

lemma scaled_numerator_integral (n k : ℕ) :
    RatIntegral ((3 : ℚ) ^ (n - 1) *
      ((numeratorPoly n).eval (pole k) / (pole k) ^ (n - 1))) := by
  rw [scaled_numerator_eq_intCast]
  exact RatIntegral.intCast _

lemma prod_range_reverse {M : Type*} [CommMonoid M] (f : ℕ → M) (n : ℕ) :
    (∏ j ∈ Finset.range n, f (n - j)) =
      ∏ j ∈ Finset.range n, f (j + 1) := by
  convert Finset.prod_range_reflect (fun r => f (r + 1)) n using 1
  apply Finset.prod_congr rfl
  intro j hj
  congr 1
  simp only [Finset.mem_range] at hj
  omega

lemma prod_range_erase_eq_left_mul_right {M : Type*} [CommMonoid M]
    (f : ℕ → M) {n k : ℕ} (hk : k < n) :
    (∏ l ∈ (Finset.range n).erase k, f l) =
      (∏ l ∈ Finset.range k, f l) *
        ∏ r ∈ Finset.range (n - 1 - k), f (k + 1 + r) := by
  have herase : (Finset.range n).erase k =
      Finset.range k ∪ Finset.Ico (k + 1) n := by
    ext l
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
  rw [herase, Finset.prod_union]
  · rw [Finset.prod_Ico_eq_prod_range]
    rw [show n - (k + 1) = n - 1 - k by omega]
  · exact Finset.disjoint_left.mpr fun l hlower hupper => by
      simp only [Finset.mem_range] at hlower
      simp only [Finset.mem_Ico] at hupper
      omega

lemma poleFactor_eval_eq_ratio (k l : ℕ) :
    (poleFactor l).eval (pole k) =
      1 - (2 : ℚ) ^ (l + 1) / (2 : ℚ) ^ (k + 1) := by
  simp only [poleFactor, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  rw [pole, cRat]
  field_simp

/-- The exponent of two arising from the factors below the `k`th pole. -/
def triangular (k : ℕ) : ℕ := ∑ r ∈ Finset.range k, (r + 1)

lemma poleFactor_eval_left {k l : ℕ} (hlk : l < k) :
    (poleFactor l).eval (pole k) =
      ((2 : ℚ) ^ (k - l) - 1) / (2 : ℚ) ^ (k - l) := by
  rw [poleFactor_eval_eq_ratio]
  have hpow : (2 : ℚ) ^ (k + 1) = (2 : ℚ) ^ (l + 1) * (2 : ℚ) ^ (k - l) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow]
  field_simp

lemma poleFactor_eval_right (k r : ℕ) :
    (poleFactor (k + 1 + r)).eval (pole k) =
      -(2 ^ (r + 1) - 1 : ℚ) := by
  rw [poleFactor_eval_eq_ratio]
  have hpow : (2 : ℚ) ^ (k + 1 + r + 1) =
      (2 : ℚ) ^ (k + 1) * (2 : ℚ) ^ (r + 1) := by
    rw [← pow_add]
    congr 1
  rw [hpow]
  field_simp
  ring

lemma poleRest_eval_formula {n k : ℕ} (hk : k < n) :
    (poleRest n k).eval (pole k) =
      ((oddProduct k : ℚ) / (2 : ℚ) ^ triangular k) *
        ((-1 : ℚ) ^ (n - 1 - k) * (oddProduct (n - 1 - k) : ℚ)) := by
  rw [poleRest, Polynomial.eval_prod]
  rw [prod_range_erase_eq_left_mul_right
    (fun l => (poleFactor l).eval (pole k)) hk]
  congr 1
  · have hleft :
        (∏ l ∈ Finset.range k, (poleFactor l).eval (pole k)) =
          ∏ l ∈ Finset.range k,
            (((2 : ℚ) ^ (k - l) - 1) / (2 : ℚ) ^ (k - l)) := by
          apply Finset.prod_congr rfl
          intro l hl
          exact poleFactor_eval_left (Finset.mem_range.mp hl)
    rw [hleft, prod_range_reverse
      (fun d => (((2 : ℚ) ^ d - 1) / (2 : ℚ) ^ d)) k]
    rw [Finset.prod_div_distrib]
    congr 1
    · rw [oddProduct, Nat.cast_prod]
      apply Finset.prod_congr rfl
      intro r hr
      rw [Nat.cast_sub]
      · norm_num
      · exact one_le_pow₀ (by omega)
    · rw [triangular, Finset.prod_pow_eq_pow_sum]
  · rw [show (∏ r ∈ Finset.range (n - 1 - k),
        (poleFactor (k + 1 + r)).eval (pole k)) =
        ∏ r ∈ Finset.range (n - 1 - k), -(2 ^ (r + 1) - 1 : ℚ) by
          apply Finset.prod_congr rfl
          intro r hr
          exact poleFactor_eval_right k r]
    rw [Finset.prod_neg, Finset.card_range]
    congr 1
    rw [oddProduct, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro r hr
    rw [Nat.cast_sub]
    · norm_num
    · exact one_le_pow₀ (by omega)

lemma oddProduct_pos (s : ℕ) : 0 < oddProduct s := by
  rw [oddProduct]
  apply Finset.prod_pos
  intro r hr
  have hpow : 1 < 2 ^ (r + 1) := one_lt_pow₀ (by omega) (by omega)
  omega

lemma oddCommon_div_poleRest_integral {n k : ℕ} (hk : k < n) :
    RatIntegral ((oddCommon n : ℚ) / (poleRest n k).eval (pole k)) := by
  obtain ⟨q, hq⟩ := pole_odd_denominator_dvd hk
  let s := n - 1 - k
  refine ⟨((q * 2 ^ triangular k : ℕ) : ℤ) * (-1 : ℤ) ^ s, ?_⟩
  rw [poleRest_eval_formula hk, hq]
  push_cast
  have hkodd : (oddProduct k : ℚ) ≠ 0 := by exact_mod_cast (oddProduct_pos k).ne'
  have hsodd : (oddProduct s : ℚ) ≠ 0 := by exact_mod_cast (oddProduct_pos s).ne'
  have htwo : (2 : ℚ) ^ triangular k ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp [s, hkodd, hsodd, htwo]
  have hsign : ((-1 : ℚ) ^ (n - 1 - k)) ^ 2 = 1 := by
    rw [← pow_mul]
    simp
  calc
    (q : ℚ) = (q : ℚ) * 1 := by ring
    _ = (q : ℚ) * ((-1 : ℚ) ^ (n - 1 - k)) ^ 2 := by rw [hsign]
    _ = (q : ℚ) * (-1 : ℚ) ^ (n - 1 - k) * (-1 : ℚ) ^ s := by
      simp only [s, pow_two]
      ring

lemma scaled_poleCoeff_integral (N k : ℕ) (hk : k < N + 2) :
    RatIntegral ((3 : ℚ) ^ (N + 2) * (oddCommon (N + 2) : ℚ) * poleCoeff N k) := by
  have hnum := scaled_numerator_integral (N + 2) k
  have hrest := oddCommon_div_poleRest_integral hk
  have hprod := (RatIntegral.intCast 3).mul (hnum.mul hrest)
  convert hprod using 1
  rw [poleCoeff_eq_eval_div N hk]
  field_simp [pole_ne_zero, poleRest_eval_ne_zero]
  norm_num [show N + 2 - 1 = N + 1 by omega,
    show 2 + N - 1 = N + 1 by omega,
    show 2 + N = N + 2 by omega, pow_succ]
  ring

/-- The value of Borwein's kernel at `X = 2^m`. -/
def kernel (n m : ℕ) : ℝ :=
  (((numeratorPoly n).eval ((2 : ℚ) ^ m) /
    (((2 : ℚ) ^ m) ^ (n - 1) *
      (denominatorPoly n).eval ((2 : ℚ) ^ m)) : ℚ) : ℝ)

/-- The tail of Borwein's kernel. -/
def kernelTail (n : ℕ) : ℝ :=
  ∑' s : ℕ, kernel n (n + s)

lemma kernel_eq_product (n m : ℕ) :
    kernel n m =
      - (∏ j ∈ Finset.range (n - 1),
          (1 - (2 : ℝ) ^ (j + 1) / (2 : ℝ) ^ m)) /
        (∏ k ∈ Finset.range n,
          (1 - (8 / 3 : ℝ) * (2 : ℝ) ^ (k + 1 + m))) := by
  rw [kernel, numeratorPoly, denominatorPoly, Polynomial.eval_neg,
    Polynomial.eval_prod, Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_one, Rat.cast_div, Rat.cast_neg,
    Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat]
  push_cast
  have hnum :
      (∏ j ∈ Finset.range (n - 1),
          ((2 : ℝ) ^ m - (2 : ℝ) ^ (j + 1))) /
          ((2 : ℝ) ^ m) ^ (n - 1) =
        ∏ j ∈ Finset.range (n - 1),
          (1 - (2 : ℝ) ^ (j + 1) / (2 : ℝ) ^ m) := by
    rw [← show (∏ _j ∈ Finset.range (n - 1), (2 : ℝ) ^ m) =
        ((2 : ℝ) ^ m) ^ (n - 1) by simp]
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro j hj
    field_simp
  have hden :
      (∏ k ∈ Finset.range n,
          (1 - (cRat : ℝ) * (2 : ℝ) ^ (k + 1) * (2 : ℝ) ^ m)) =
        ∏ k ∈ Finset.range n,
          (1 - (8 / 3 : ℝ) * (2 : ℝ) ^ (k + 1 + m)) := by
    apply Finset.prod_congr rfl
    intro k hk
    rw [cRat]
    push_cast
    rw [pow_add]
    ring
  rw [hden]
  simp only [neg_div]
  rw [show (∏ j ∈ Finset.range (n - 1),
          ((2 : ℝ) ^ m - (2 : ℝ) ^ (j + 1))) /
        (((2 : ℝ) ^ m) ^ (n - 1) *
          ∏ k ∈ Finset.range n,
            (1 - (8 / 3 : ℝ) * (2 : ℝ) ^ (k + 1 + m))) =
      ((∏ j ∈ Finset.range (n - 1),
          ((2 : ℝ) ^ m - (2 : ℝ) ^ (j + 1))) /
        ((2 : ℝ) ^ m) ^ (n - 1)) /
          ∏ k ∈ Finset.range n,
            (1 - (8 / 3 : ℝ) * (2 : ℝ) ^ (k + 1 + m)) by
        simp only [div_eq_mul_inv]
        ring]
  rw [hnum]

lemma numeratorPoly_partial_fraction_identity (N : ℕ) :
    numeratorPoly (N + 2) =
      principalPoly (N + 2) * denominatorPoly (N + 2) +
        Polynomial.X ^ (N + 1) * simplePolePoly N := by
  rw [show principalPoly (N + 2) * denominatorPoly (N + 2) +
      Polynomial.X ^ (N + 1) * simplePolePoly N =
      Polynomial.X ^ (N + 1) * simplePolePoly N +
        principalPoly (N + 2) * denominatorPoly (N + 2) by ring]
  rw [← sub_eq_iff_eq_add]
  change remainderPoly (N + 2) =
    Polynomial.X ^ (N + 1) * simplePolePoly N
  rw [residualPoly_spec, residualPoly_eq_simplePolePoly]

lemma poleFactor_eval_two_pow_neg (k m : ℕ) :
    (poleFactor k).eval ((2 : ℚ) ^ m) < 0 := by
  simp only [poleFactor, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  rw [cRat]
  rw [show (8 / 3 : ℚ) * 2 ^ (k + 1) * 2 ^ m =
      (8 / 3 : ℚ) * 2 ^ (k + 1 + m) by rw [mul_assoc, ← pow_add]]
  have hp : (1 : ℚ) ≤ 2 ^ (k + 1 + m) := one_le_pow₀ (by norm_num)
  norm_num at hp ⊢
  nlinarith

lemma denominatorPoly_eval_two_pow_ne_zero (n m : ℕ) :
    (denominatorPoly n).eval ((2 : ℚ) ^ m) ≠ 0 := by
  rw [denominatorPoly, Polynomial.eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  exact (poleFactor_eval_two_pow_neg k m).ne

lemma poleRest_eval_two_pow_ne_zero (n k m : ℕ) :
    (poleRest n k).eval ((2 : ℚ) ^ m) ≠ 0 := by
  rw [poleRest, Polynomial.eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro l hl
  exact (poleFactor_eval_two_pow_neg l m).ne

lemma simplePolePoly_div_denominator (N m : ℕ) :
    (simplePolePoly N).eval ((2 : ℚ) ^ m) /
        (denominatorPoly (N + 2)).eval ((2 : ℚ) ^ m) =
      ∑ k ∈ Finset.range (N + 2),
        poleCoeff N k / (poleFactor k).eval ((2 : ℚ) ^ m) := by
  rw [simplePolePoly, Polynomial.eval_finsetSum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  rw [denominatorPoly_eq_factor_mul_rest hk]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  field_simp [(poleFactor_eval_two_pow_neg k m).ne,
    poleRest_eval_two_pow_ne_zero (N + 2) k m]

lemma rational_partial_fraction (N m : ℕ) :
    (numeratorPoly (N + 2)).eval ((2 : ℚ) ^ m) /
        (((2 : ℚ) ^ m) ^ (N + 1) *
          (denominatorPoly (N + 2)).eval ((2 : ℚ) ^ m)) =
      (principalPoly (N + 2)).eval ((2 : ℚ) ^ m) /
          ((2 : ℚ) ^ m) ^ (N + 1) +
        ∑ k ∈ Finset.range (N + 2),
          poleCoeff N k / (poleFactor k).eval ((2 : ℚ) ^ m) := by
  have hid := congrArg (Polynomial.eval ((2 : ℚ) ^ m))
    (numeratorPoly_partial_fraction_identity N)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X] at hid
  rw [← simplePolePoly_div_denominator]
  have hx : (2 : ℚ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
  have hD := denominatorPoly_eval_two_pow_ne_zero (N + 2) m
  field_simp [hx, hD]
  linear_combination hid

/-! ## Summing the partial fractions -/

/-- The real principal-part summand at `m = t+1`. -/
def principalAt (N t : ℕ) : ℝ :=
  (((principalPoly (N + 2)).eval ((2 : ℚ) ^ (t + 1)) /
    ((2 : ℚ) ^ (t + 1)) ^ (N + 1) : ℚ) : ℝ)

/-- The sum of the kernel over all positive powers of two. -/
def kernelAll (N : ℕ) : ℝ :=
  ∑' t : ℕ, kernel (N + 2) (t + 1)

lemma pole_fraction_cast (k m : ℕ) :
    (((1 : ℚ) / (poleFactor k).eval ((2 : ℚ) ^ m) : ℚ) : ℝ) =
      shiftedTerm (k + m) := by
  rw [poleFactor, shiftedTerm, cRat]
  simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Rat.cast_div, Rat.cast_one,
    Rat.cast_sub, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat]
  rw [show (8 / 3 : ℝ) * (2 : ℝ) ^ (k + 1) * (2 : ℝ) ^ m =
      (8 / 3 : ℝ) * (2 : ℝ) ^ (k + m + 1) by
        rw [mul_assoc, ← pow_add,
          show k + 1 + m = k + m + 1 by omega]]

lemma kernel_partial_fraction_real (N t : ℕ) :
    kernel (N + 2) (t + 1) = principalAt N t +
      ∑ k ∈ Finset.range (N + 2),
        (poleCoeff N k : ℝ) * shiftedTerm (k + t + 1) := by
  have h := congrArg (fun x : ℚ => (x : ℝ)) (rational_partial_fraction N (t + 1))
  rw [kernel, principalAt]
  push_cast at h ⊢
  rw [h]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [div_eq_mul_inv]
  rw [show (↑((poleFactor k).eval ((2 : ℚ) ^ (t + 1))) : ℝ)⁻¹ =
      shiftedTerm (k + (t + 1)) by
        simpa only [one_div, Rat.cast_inv] using pole_fraction_cast k (t + 1)]
  congr 2

lemma principalAt_eq_sum (N t : ℕ) :
    principalAt N t =
      ∑ r ∈ Finset.range (N + 1),
        (principalCoeff (N + 2) r : ℝ) *
          ((1 / 2 : ℝ) ^ (N + 1 - r)) ^ (t + 1) := by
  rw [principalAt]
  have heval := Polynomial.eval_eq_sum_range'
    (principalPoly_natDegree_lt (N + 2) (by omega)) ((2 : ℚ) ^ (t + 1))
  rw [heval, Finset.sum_div]
  push_cast
  apply Finset.sum_congr rfl
  intro r hr
  have hrlt : r < N + 1 := Finset.mem_range.mp hr
  rw [principalPoly_coeff (N + 2) r (by omega)]
  have hx : (2 : ℝ) ^ (t + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hpow : ((2 : ℝ) ^ (t + 1)) ^ (N + 1) =
      ((2 : ℝ) ^ (t + 1)) ^ r *
        ((2 : ℝ) ^ (t + 1)) ^ (N + 1 - r) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow]
  field_simp [hx]
  rw [← pow_mul, ← pow_mul]
  rw [one_div_pow]
  field_simp
  rw [Nat.mul_comm (t + 1) (N + 1 - r)]

lemma half_pow_norm_lt_one {d : ℕ} (hd : 0 < d) :
    ‖(1 / 2 : ℝ) ^ d‖ < 1 := by
  rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  exact pow_lt_one₀ (by norm_num) (by norm_num) hd.ne'

lemma summable_finsetSum_local {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℝ)
    (hf : ∀ i ∈ s, Summable (f i)) :
    Summable (fun n => ∑ i ∈ s, f i n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simpa only [Finset.sum_insert hi] using
        (hf i (Finset.mem_insert_self i s)).add
          (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

lemma summable_principal_monomial (N r : ℕ) (hr : r < N + 1) :
    Summable (fun t : ℕ =>
      (principalCoeff (N + 2) r : ℝ) *
        ((1 / 2 : ℝ) ^ (N + 1 - r)) ^ (t + 1)) := by
  let z : ℝ := (1 / 2 : ℝ) ^ (N + 1 - r)
  have hz : ‖z‖ < 1 := half_pow_norm_lt_one (by omega)
  have hs := (summable_geometric_of_norm_lt_one (K := ℝ) hz).mul_left
    ((principalCoeff (N + 2) r : ℝ) * z)
  apply hs.congr
  intro t
  simp only [z, pow_succ]
  ring

lemma summable_principalAt (N : ℕ) : Summable (principalAt N) := by
  apply (summable_finsetSum_local (Finset.range (N + 1))
    (fun r t => (principalCoeff (N + 2) r : ℝ) *
      ((1 / 2 : ℝ) ^ (N + 1 - r)) ^ (t + 1))
    (fun r hr => summable_principal_monomial N r (Finset.mem_range.mp hr))).congr
  intro t
  exact (principalAt_eq_sum N t).symm

lemma tsum_half_pow_succ {d : ℕ} (hd : 0 < d) :
    (∑' t : ℕ, ((1 / 2 : ℝ) ^ d) ^ (t + 1)) =
      1 / ((2 : ℝ) ^ d - 1) := by
  let z : ℝ := (1 / 2 : ℝ) ^ d
  have hz : ‖z‖ < 1 := half_pow_norm_lt_one hd
  change (∑' t : ℕ, z ^ (t + 1)) = 1 / ((2 : ℝ) ^ d - 1)
  calc
    (∑' t : ℕ, z ^ (t + 1)) = z * ∑' t : ℕ, z ^ t := by
          rw [← tsum_mul_left]
          apply tsum_congr
          intro t
          rw [pow_succ]
          rw [mul_comm]
    _ = z * (1 - z)⁻¹ := by rw [tsum_geometric_of_norm_lt_one hz]
    _ = 1 / ((2 : ℝ) ^ d - 1) := by
      dsimp only [z]
      rw [one_div_pow]
      have hp : (2 : ℝ) ^ d ≠ 0 := pow_ne_zero _ (by norm_num)
      field_simp [hp]

/-- The rational constant contributed by the principal part. -/
def principalConstant (N : ℕ) : ℝ :=
  ∑ r ∈ Finset.range (N + 1),
    (principalCoeff (N + 2) r : ℝ) /
      ((2 : ℝ) ^ (N + 1 - r) - 1)

lemma tsum_principalAt (N : ℕ) :
    (∑' t : ℕ, principalAt N t) = principalConstant N := by
  rw [tsum_congr (principalAt_eq_sum N)]
  rw [Summable.tsum_finsetSum (fun r hr =>
    summable_principal_monomial N r (Finset.mem_range.mp hr))]
  rw [principalConstant]
  apply Finset.sum_congr rfl
  intro r hr
  rw [tsum_mul_left]
  rw [tsum_half_pow_succ (Nat.sub_pos_of_lt (Finset.mem_range.mp hr))]
  simp only [div_eq_mul_inv, one_mul]

/-- The finite initial segment removed from `shiftedValue`. -/
def shiftPrefix (k : ℕ) : ℝ :=
  ∑ h ∈ Finset.range (k + 1), shiftedTerm h

lemma summable_shifted_pole (N k : ℕ) :
    Summable (fun t : ℕ =>
      (poleCoeff N k : ℝ) * shiftedTerm (k + t + 1)) := by
  have hs : Summable (fun t : ℕ => shiftedTerm (t + (k + 1))) :=
    (summable_nat_add_iff (k + 1)).2 summable_shifted
  apply (hs.mul_left (poleCoeff N k : ℝ)).congr
  intro t
  congr 2
  omega

lemma tsum_shifted_tail (k : ℕ) :
    (∑' t : ℕ, shiftedTerm (k + t + 1)) = shiftedValue - shiftPrefix k := by
  have hsplit := summable_shifted.sum_add_tsum_nat_add (k + 1)
  have htail : (∑' t : ℕ, shiftedTerm (k + t + 1)) =
      ∑' t : ℕ, shiftedTerm (t + (k + 1)) := by
    apply tsum_congr
    intro t
    congr 1
    omega
  rw [shiftedValue, shiftPrefix]
  rw [htail]
  linarith

lemma tsum_pole_part (N : ℕ) :
    (∑' t : ℕ, ∑ k ∈ Finset.range (N + 2),
      (poleCoeff N k : ℝ) * shiftedTerm (k + t + 1)) =
      ∑ k ∈ Finset.range (N + 2),
        (poleCoeff N k : ℝ) * (shiftedValue - shiftPrefix k) := by
  rw [Summable.tsum_finsetSum (fun k _ => summable_shifted_pole N k)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [tsum_mul_left, tsum_shifted_tail]

lemma summable_kernelAll (N : ℕ) :
    Summable (fun t : ℕ => kernel (N + 2) (t + 1)) := by
  apply (summable_principalAt N).add
    (summable_finsetSum_local (Finset.range (N + 2))
      (fun k t => (poleCoeff N k : ℝ) * shiftedTerm (k + t + 1))
      (fun k _ => summable_shifted_pole N k)) |>.congr
  intro t
  exact (kernel_partial_fraction_real N t).symm

lemma kernelAll_linear_form (N : ℕ) :
    kernelAll N = principalConstant N +
      ∑ k ∈ Finset.range (N + 2),
        (poleCoeff N k : ℝ) * (shiftedValue - shiftPrefix k) := by
  rw [kernelAll]
  rw [tsum_congr (kernel_partial_fraction_real N)]
  rw [(summable_principalAt N).tsum_add
    (summable_finsetSum_local (Finset.range (N + 2))
      (fun k t => (poleCoeff N k : ℝ) * shiftedTerm (k + t + 1))
      (fun k _ => summable_shifted_pole N k))]
  rw [tsum_principalAt, tsum_pole_part]

lemma kernel_early_zero (N t : ℕ) (ht : t < N + 1) :
    kernel (N + 2) (t + 1) = 0 := by
  rw [kernel_eq_product]
  have hmem : t ∈ Finset.range (N + 2 - 1) := by
    simp only [Finset.mem_range]
    omega
  rw [Finset.prod_eq_zero hmem]
  · simp
  · norm_num

lemma kernelAll_eq_kernelTail (N : ℕ) :
    kernelAll N = kernelTail (N + 2) := by
  have hsplit := (summable_kernelAll N).sum_add_tsum_nat_add (N + 1)
  rw [kernelAll, kernelTail]
  rw [← hsplit]
  have hfin : (∑ t ∈ Finset.range (N + 1), kernel (N + 2) (t + 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    exact kernel_early_zero N t (Finset.mem_range.mp ht)
  rw [hfin, zero_add]
  apply tsum_congr
  intro t
  exact congrArg (kernel (N + 2)) (by omega)

lemma summable_kernelTail (N : ℕ) :
    Summable (fun s : ℕ => kernel (N + 2) (N + 2 + s)) := by
  have hs : Summable (fun t : ℕ => kernel (N + 2) (t + 1)) := summable_kernelAll N
  have hi : Function.Injective (fun s : ℕ => N + 1 + s) := fun _ _ h =>
    Nat.add_left_cancel h
  have ht := hs.comp_injective hi
  apply ht.congr
  intro s
  change kernel (N + 2) (N + 1 + s + 1) = kernel (N + 2) (N + 2 + s)
  exact congrArg (kernel (N + 2)) (by omega)

/-! ## Fixed sign and nonvanishing -/

lemma numerator_product_pos {n m : ℕ} (hn : 2 ≤ n) (hm : n ≤ m) :
    0 < ∏ j ∈ Finset.range (n - 1),
      (1 - (2 : ℝ) ^ (j + 1) / (2 : ℝ) ^ m) := by
  apply Finset.prod_pos
  intro j hj
  have hjm : j + 1 < m := by
    have := Finset.mem_range.mp hj
    omega
  have hp : (2 : ℝ) ^ (j + 1) < (2 : ℝ) ^ m :=
    pow_lt_pow_right₀ (by norm_num) hjm
  exact sub_pos.mpr ((div_lt_one (by positivity)).2 hp)

lemma signed_denominator_product_pos (n m : ℕ) :
    0 < (-1 : ℝ) ^ n *
      (∏ k ∈ Finset.range n,
        (1 - (8 / 3 : ℝ) * (2 : ℝ) ^ (k + 1 + m))) := by
  rw [show (-1 : ℝ) ^ n = ∏ _k ∈ Finset.range n, (-1 : ℝ) by simp]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_pos
  intro k hk
  have hp : (1 : ℝ) ≤ 2 ^ (k + 1 + m) := one_le_pow₀ (by norm_num)
  norm_num at hp ⊢
  nlinarith

lemma signed_kernel_pos (N s : ℕ) :
    0 < (-1 : ℝ) ^ (N + 3) * kernel (N + 2) (N + 2 + s) := by
  rw [kernel_eq_product]
  let A : ℝ := ∏ j ∈ Finset.range (N + 2 - 1),
    (1 - (2 : ℝ) ^ (j + 1) / (2 : ℝ) ^ (N + 2 + s))
  let D : ℝ := ∏ k ∈ Finset.range (N + 2),
    (1 - (8 / 3 : ℝ) * (2 : ℝ) ^ (k + 1 + (N + 2 + s)))
  have hA : 0 < A := numerator_product_pos (by omega) (by omega)
  have hD : 0 < (-1 : ℝ) ^ (N + 2) * D :=
    signed_denominator_product_pos (N + 2) (N + 2 + s)
  have hDn : D ≠ 0 := by
    intro h
    rw [h, mul_zero] at hD
    exact lt_irrefl 0 hD
  change 0 < (-1 : ℝ) ^ (N + 3) * (-A / D)
  have hsquare : (-1 : ℝ) ^ (N + 2) * (-1 : ℝ) ^ (N + 2) = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨N + 2, by omega⟩
  rw [show (-1 : ℝ) ^ (N + 3) * (-A / D) =
      A / ((-1 : ℝ) ^ (N + 2) * D) by
        field_simp [hDn]
        rw [pow_succ]
        nlinarith]
  exact div_pos hA hD

lemma kernelTail_ne_zero (N : ℕ) : kernelTail (N + 2) ≠ 0 := by
  let sign : ℝ := (-1 : ℝ) ^ (N + 3)
  have hs : Summable (fun s : ℕ => sign * kernel (N + 2) (N + 2 + s)) :=
    (summable_kernelTail N).mul_left sign
  have hpos : 0 < ∑' s : ℕ, sign * kernel (N + 2) (N + 2 + s) :=
    hs.tsum_pos (fun s => (signed_kernel_pos N s).le) 0 (signed_kernel_pos N 0)
  rw [tsum_mul_left] at hpos
  change 0 < sign * kernelTail (N + 2) at hpos
  exact fun h => by rw [h, mul_zero] at hpos; exact lt_irrefl 0 hpos

/-! ## Quantitative decay of the kernel tail -/

/-- The total power of two contributed by the denominator lower bound. -/
def kernelExponent (n m : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, (k + 1 + m)

lemma kernelExponent_add (n m s : ℕ) :
    kernelExponent n (m + s) = kernelExponent n m + n * s := by
  simp [kernelExponent, add_assoc, Finset.sum_add_distrib]
  ring

lemma numerator_product_abs_le_one {n m : ℕ} (hm : n ≤ m) :
    |∏ j ∈ Finset.range (n - 1),
      (1 - (2 : ℝ) ^ (j + 1) / (2 : ℝ) ^ m)| ≤ 1 := by
  rw [Finset.abs_prod]
  apply Finset.prod_le_one
  · intro j hj
    exact abs_nonneg _
  · intro j hj
    have hjm : j + 1 < m := by
      have := Finset.mem_range.mp hj
      omega
    have hpos : 0 < 1 - (2 : ℝ) ^ (j + 1) / (2 : ℝ) ^ m :=
      sub_pos.mpr ((div_lt_one (by positivity)).2
        (pow_lt_pow_right₀ (by norm_num) hjm))
    rw [abs_of_pos hpos]
    exact sub_le_self _ (by positivity)

lemma denominator_factor_abs_lower (k m : ℕ) :
    (2 : ℝ) ^ (k + 1 + m) ≤
      |1 - (8 / 3 : ℝ) * (2 : ℝ) ^ (k + 1 + m)| := by
  have hp : (1 : ℝ) ≤ 2 ^ (k + 1 + m) := one_le_pow₀ (by norm_num)
  have hneg : 1 - (8 / 3 : ℝ) * 2 ^ (k + 1 + m) < 0 := by
    norm_num at hp ⊢
    nlinarith
  rw [abs_of_neg hneg]
  nlinarith

lemma denominator_product_abs_lower (n m : ℕ) :
    (2 : ℝ) ^ kernelExponent n m ≤
      |∏ k ∈ Finset.range n,
        (1 - (8 / 3 : ℝ) * (2 : ℝ) ^ (k + 1 + m))| := by
  rw [kernelExponent, ← Finset.prod_pow_eq_pow_sum, Finset.abs_prod]
  exact Finset.prod_le_prod (fun k hk => by positivity)
    (fun k hk => denominator_factor_abs_lower k m)

lemma abs_kernel_le (n m : ℕ) (hm : n ≤ m) :
    |kernel n m| ≤ 1 / (2 : ℝ) ^ kernelExponent n m := by
  rw [kernel_eq_product, abs_div, abs_neg]
  let A : ℝ := |∏ j ∈ Finset.range (n - 1),
    (1 - (2 : ℝ) ^ (j + 1) / (2 : ℝ) ^ m)|
  let D : ℝ := |∏ k ∈ Finset.range n,
    (1 - (8 / 3 : ℝ) * (2 : ℝ) ^ (k + 1 + m))|
  have hA : A ≤ 1 := numerator_product_abs_le_one hm
  have hD : (2 : ℝ) ^ kernelExponent n m ≤ D := denominator_product_abs_lower n m
  have hDp : 0 < D := lt_of_lt_of_le (by positivity) hD
  calc
    A / D ≤ (1 : ℝ) / D := (div_le_div_iff_of_pos_right hDp).2 hA
    _ ≤ (1 : ℝ) / (2 : ℝ) ^ kernelExponent n m :=
      one_div_le_one_div_of_le (by positivity) hD

lemma abs_kernel_tail_term_le (N s : ℕ) :
    |kernel (N + 2) (N + 2 + s)| ≤
      (1 / (2 : ℝ) ^ kernelExponent (N + 2) (N + 2)) *
        (1 / (2 : ℝ) ^ (N + 2)) ^ s := by
  calc
    |kernel (N + 2) (N + 2 + s)| ≤
        1 / (2 : ℝ) ^ kernelExponent (N + 2) (N + 2 + s) :=
      abs_kernel_le _ _ (by omega)
    _ = (1 / (2 : ℝ) ^ kernelExponent (N + 2) (N + 2)) *
        (1 / (2 : ℝ) ^ (N + 2)) ^ s := by
      rw [kernelExponent_add]
      rw [pow_add]
      simp only [one_div_pow, pow_mul]
      rw [one_div_mul_one_div_rev]
      congr 1
      ac_rfl

lemma summable_abs_kernel_tail (N : ℕ) :
    Summable (fun s : ℕ => |kernel (N + 2) (N + 2 + s)|) := by
  apply Summable.of_nonneg_of_le (fun s => abs_nonneg _)
    (abs_kernel_tail_term_le N)
  apply (summable_geometric_of_norm_lt_one (K := ℝ)
    (x := 1 / (2 : ℝ) ^ (N + 2)) ?_).mul_left
  rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [one_div]
  exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ (by norm_num) (by omega))

lemma abs_kernelTail_le (N : ℕ) :
    |kernelTail (N + 2)| ≤
      2 / (2 : ℝ) ^ kernelExponent (N + 2) (N + 2) := by
  have hnorm : Summable (fun s : ℕ => ‖kernel (N + 2) (N + 2 + s)‖) := by
    simpa [Real.norm_eq_abs] using summable_abs_kernel_tail N
  calc
    |kernelTail (N + 2)| ≤
        ∑' s : ℕ, |kernel (N + 2) (N + 2 + s)| := by
      rw [kernelTail, ← Real.norm_eq_abs]
      simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' s : ℕ,
        (1 / (2 : ℝ) ^ kernelExponent (N + 2) (N + 2)) *
          (1 / (2 : ℝ) ^ (N + 2)) ^ s := by
      exact (summable_abs_kernel_tail N).tsum_le_tsum (abs_kernel_tail_term_le N)
        ((summable_geometric_of_norm_lt_one (K := ℝ)
          (x := 1 / (2 : ℝ) ^ (N + 2)) (by
            rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
            rw [one_div]
            exact inv_lt_one_of_one_lt₀
              (one_lt_pow₀ (by norm_num) (by omega)))).mul_left _)
    _ ≤ 2 / (2 : ℝ) ^ kernelExponent (N + 2) (N + 2) := by
      rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (by
        rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
        rw [one_div]
        exact inv_lt_one_of_one_lt₀
          (one_lt_pow₀ (by norm_num) (by omega)))]
      have hz : 0 ≤ (1 / (2 : ℝ) ^ (N + 2)) := by positivity
      have hzhalf : (1 / (2 : ℝ) ^ (N + 2)) ≤ 1 / 2 := by
        have hpow : (2 : ℝ) ≤ 2 ^ (N + 2) := by
          calc
            (2 : ℝ) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (N + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
        exact one_div_le_one_div_of_le (by norm_num) hpow
      have hinv : (1 - (1 / (2 : ℝ) ^ (N + 2)))⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ (by nlinarith) (by norm_num)]
        norm_num [one_div] at hzhalf ⊢
        nlinarith
      have hC : 0 ≤ (1 / (2 : ℝ) ^ kernelExponent (N + 2) (N + 2)) := by
        positivity
      calc
        (1 / (2 : ℝ) ^ kernelExponent (N + 2) (N + 2)) *
              (1 - 1 / (2 : ℝ) ^ (N + 2))⁻¹ ≤
            (1 / (2 : ℝ) ^ kernelExponent (N + 2) (N + 2)) * 2 :=
          mul_le_mul_of_nonneg_left hinv hC
        _ = 2 / (2 : ℝ) ^ kernelExponent (N + 2) (N + 2) := by ring

/-! ## Integer linear forms -/

/-- The rational version of `shiftedTerm`. -/
def shiftedTermRat (h : ℕ) : ℚ :=
  1 / (1 - cRat * (2 : ℚ) ^ (h + 1))

/-- The rational finite prefix removed from the shifted series. -/
def shiftPrefixRat (k : ℕ) : ℚ :=
  ∑ h ∈ Finset.range (k + 1), shiftedTermRat h

/-- The rational version of the principal constant. -/
def principalConstantRat (N : ℕ) : ℚ :=
  ∑ r ∈ Finset.range (N + 1),
    principalCoeff (N + 2) r /
      ((2 : ℚ) ^ (N + 1 - r) - 1)

lemma shiftedTermRat_cast (h : ℕ) : (shiftedTermRat h : ℝ) = shiftedTerm h := by
  simp [shiftedTermRat, shiftedTerm, cRat]

lemma shiftPrefixRat_cast (k : ℕ) : (shiftPrefixRat k : ℝ) = shiftPrefix k := by
  simp [shiftPrefixRat, shiftPrefix, shiftedTermRat_cast]

lemma principalConstantRat_cast (N : ℕ) :
    (principalConstantRat N : ℝ) = principalConstant N := by
  simp [principalConstantRat, principalConstant]

/-- A common denominator for the finite shifted prefixes. -/
def shiftCommon (n : ℕ) : ℕ :=
  ∏ h ∈ Finset.range n, (2 ^ (h + 4) - 3)

/-- The full positive integer multiplier for the order-`n` linear form. -/
def commonMultiplier (n : ℕ) : ℕ :=
  3 ^ n * oddCommon n * shiftCommon n

lemma shiftedTermRat_eq (h : ℕ) :
    shiftedTermRat h = -(3 : ℚ) / (2 ^ (h + 4) - 3 : ℕ) := by
  rw [shiftedTermRat, cRat]
  have hp : 3 ≤ 2 ^ (h + 4) := by
    calc
      3 ≤ 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (h + 4) := Nat.pow_le_pow_right (by omega) (by omega)
  rw [Nat.cast_sub hp]
  push_cast
  rw [show (2 : ℚ) ^ (h + 4) = 8 * (2 : ℚ) ^ (h + 1) by
    rw [show h + 4 = 3 + (h + 1) by omega, pow_add]
    norm_num]
  have hx : (1 : ℚ) ≤ 2 ^ (h + 1) := one_le_pow₀ (by norm_num)
  have hden : 8 * (2 : ℚ) ^ (h + 1) - 3 ≠ 0 := by nlinarith
  apply (eq_div_iff hden).2
  rw [show 1 - 8 / 3 * (2 : ℚ) ^ (h + 1) =
      -(8 * (2 : ℚ) ^ (h + 1) - 3) / 3 by ring]
  field_simp [hden]

lemma shiftCommon_pos (n : ℕ) : 0 < shiftCommon n := by
  rw [shiftCommon]
  apply Finset.prod_pos
  intro h hh
  have hp : 3 < 2 ^ (h + 4) := by
    calc
      3 < 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (h + 4) := Nat.pow_le_pow_right (by omega) (by omega)
  omega

lemma shift_factor_dvd {n h : ℕ} (hh : h < n) :
    2 ^ (h + 4) - 3 ∣ shiftCommon n := by
  rw [shiftCommon]
  exact Finset.dvd_prod_of_mem (fun j => 2 ^ (j + 4) - 3)
    (Finset.mem_range.mpr hh)

lemma shiftCommon_mul_shifted_integral {n h : ℕ} (hh : h < n) :
    RatIntegral ((shiftCommon n : ℚ) * shiftedTermRat h) := by
  obtain ⟨q, hq⟩ := shift_factor_dvd hh
  refine ⟨-(3 * (q : ℤ)), ?_⟩
  rw [shiftedTermRat_eq, hq]
  push_cast
  have hfacNat : 0 < 2 ^ (h + 4) - 3 := by
    have hp : 3 < 2 ^ (h + 4) := by
      calc
        3 < 2 ^ 4 := by norm_num
        _ ≤ 2 ^ (h + 4) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hfac : ((2 ^ (h + 4) - 3 : ℕ) : ℚ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr hfacNat.ne'
  field_simp [hfac]

lemma shiftCommon_mul_prefix_integral {n k : ℕ} (hk : k < n) :
    RatIntegral ((shiftCommon n : ℚ) * shiftPrefixRat k) := by
  rw [shiftPrefixRat, Finset.mul_sum]
  apply RatIntegral.sum
  intro h hh
  exact shiftCommon_mul_shifted_integral (by
    have := Finset.mem_range.mp hh
    omega)

lemma odd_factor_dvd_oddCommon {n d : ℕ} (hd0 : 0 < d) (hdn : d < n) :
    2 ^ d - 1 ∣ oddCommon n := by
  have hmem : d - 1 ∈ Finset.range (n - 1) := by
    simp only [Finset.mem_range]
    omega
  have hdiv : 2 ^ d - 1 ∣ oddProduct (n - 1) := by
    rw [oddProduct]
    have hdiv' := Finset.dvd_prod_of_mem (fun r => 2 ^ (r + 1) - 1) hmem
    have hd : d - 1 + 1 = d := by omega
    rw [hd] at hdiv'
    exact hdiv'
  exact dvd_mul_of_dvd_left hdiv _

lemma scaled_principal_fraction_integral (N r : ℕ) (hr : r < N + 1) :
    RatIntegral ((commonMultiplier (N + 2) : ℚ) *
      (principalCoeff (N + 2) r /
        ((2 : ℚ) ^ (N + 1 - r) - 1))) := by
  obtain ⟨q, hq⟩ := odd_factor_dvd_oddCommon
    (n := N + 2) (d := N + 1 - r) (by omega) (by omega)
  have hodd : ((2 : ℚ) ^ (N + 1 - r) - 1) ≠ 0 := by
    have := one_lt_pow₀ (by norm_num : (1 : ℚ) < 2) (by omega : N + 1 - r ≠ 0)
    linarith
  have heq :
      (commonMultiplier (N + 2) : ℚ) *
          (principalCoeff (N + 2) r /
            ((2 : ℚ) ^ (N + 1 - r) - 1)) =
        ((3 ^ (N + 2 - r) * q * shiftCommon (N + 2) : ℕ) : ℚ) *
          ((3 : ℚ) ^ r * principalCoeff (N + 2) r) := by
    rw [commonMultiplier, hq]
    simp only [Nat.cast_mul]
    rw [Nat.cast_sub (by exact one_le_pow₀ (by omega : 1 ≤ (2 : ℕ)))]
    push_cast
    rw [show (3 : ℚ) ^ (N + 2) = (3 : ℚ) ^ r * 3 ^ (N + 2 - r) by
      rw [← pow_add]
      congr 1
      omega]
    field_simp [hodd]
  rw [heq]
  exact (RatIntegral.intCast
    (3 ^ (N + 2 - r) * q * shiftCommon (N + 2) : ℕ)).mul
      (principalCoeff_scaled_integral (N + 2) r)

lemma commonMultiplier_mul_principal_integral (N : ℕ) :
    RatIntegral ((commonMultiplier (N + 2) : ℚ) * principalConstantRat N) := by
  rw [principalConstantRat, Finset.mul_sum]
  exact RatIntegral.sum fun r hr =>
    scaled_principal_fraction_integral N r (Finset.mem_range.mp hr)

lemma commonMultiplier_mul_pole_integral (N k : ℕ) (hk : k < N + 2) :
    RatIntegral ((commonMultiplier (N + 2) : ℚ) * poleCoeff N k) := by
  have h := (RatIntegral.intCast (shiftCommon (N + 2) : ℤ)).mul
    (scaled_poleCoeff_integral N k hk)
  convert h using 1
  rw [commonMultiplier]
  push_cast
  ring

lemma commonMultiplier_mul_pole_prefix_integral (N k : ℕ) (hk : k < N + 2) :
    RatIntegral ((commonMultiplier (N + 2) : ℚ) *
      (poleCoeff N k * shiftPrefixRat k)) := by
  have hb := scaled_poleCoeff_integral N k hk
  have hp := shiftCommon_mul_prefix_integral hk
  convert hb.mul hp using 1
  rw [commonMultiplier]
  push_cast
  ring

/-- The rational coefficient of `shiftedValue` in the cleared form. -/
def linearARat (N : ℕ) : ℚ :=
  (commonMultiplier (N + 2) : ℚ) *
    ∑ k ∈ Finset.range (N + 2), poleCoeff N k

/-- The rational constant coefficient in the cleared form. -/
def linearBRat (N : ℕ) : ℚ :=
  (commonMultiplier (N + 2) : ℚ) *
    (principalConstantRat N -
      ∑ k ∈ Finset.range (N + 2), poleCoeff N k * shiftPrefixRat k)

lemma linearARat_integral (N : ℕ) : RatIntegral (linearARat N) := by
  rw [linearARat, Finset.mul_sum]
  exact RatIntegral.sum fun k hk =>
    commonMultiplier_mul_pole_integral N k (Finset.mem_range.mp hk)

lemma linearBRat_integral (N : ℕ) : RatIntegral (linearBRat N) := by
  rw [linearBRat, mul_sub, Finset.mul_sum]
  apply (commonMultiplier_mul_principal_integral N).sub
  exact RatIntegral.sum fun k hk =>
    commonMultiplier_mul_pole_prefix_integral N k (Finset.mem_range.mp hk)

/-- The integer coefficient of the shifted Lambert value. -/
def linearA (N : ℕ) : ℤ := Classical.choose (linearARat_integral N)

/-- The integer constant coefficient. -/
def linearB (N : ℕ) : ℤ := Classical.choose (linearBRat_integral N)

lemma linearARat_eq_intCast (N : ℕ) : linearARat N = (linearA N : ℚ) :=
  Classical.choose_spec (linearARat_integral N)

lemma linearBRat_eq_intCast (N : ℕ) : linearBRat N = (linearB N : ℚ) :=
  Classical.choose_spec (linearBRat_integral N)

lemma linear_form_eq_kernelTail (N : ℕ) :
    (linearA N : ℝ) * shiftedValue + (linearB N : ℝ) =
      (commonMultiplier (N + 2) : ℝ) * kernelTail (N + 2) := by
  have hA := congrArg (fun x : ℚ => (x : ℝ)) (linearARat_eq_intCast N)
  have hB := congrArg (fun x : ℚ => (x : ℝ)) (linearBRat_eq_intCast N)
  rw [← kernelAll_eq_kernelTail]
  rw [kernelAll_linear_form]
  rw [linearARat] at hA
  rw [linearBRat] at hB
  push_cast at hA hB
  rw [← hA, ← hB]
  rw [principalConstantRat_cast]
  simp_rw [shiftPrefixRat_cast]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

lemma linear_form_ne_zero (N : ℕ) :
    (linearA N : ℝ) * shiftedValue + (linearB N : ℝ) ≠ 0 := by
  rw [linear_form_eq_kernelTail]
  apply mul_ne_zero
  · have hpos : 0 < commonMultiplier (N + 2) := by
      rw [commonMultiplier]
      exact mul_pos
        (mul_pos (pow_pos (by omega) _)
          (mul_pos (oddProduct_pos _) (oddProduct_pos _))) (shiftCommon_pos _)
    exact_mod_cast hpos.ne'
  · exact kernelTail_ne_zero N

lemma commonMultiplier_pos (n : ℕ) : 0 < commonMultiplier n := by
  rw [commonMultiplier]
  exact mul_pos (mul_pos (pow_pos (by omega) _) (mul_pos (oddProduct_pos _) (oddProduct_pos _)))
    (shiftCommon_pos _)

/-! ## Growth of the common denominator -/

lemma triangular_twice (n : ℕ) : 2 * triangular n = n * (n + 1) := by
  rw [triangular]
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      simp only [Nat.add_mul]
      nlinarith

lemma oddProduct_le_pow_two (s : ℕ) :
    oddProduct s ≤ 2 ^ triangular s := by
  rw [oddProduct, triangular, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod (fun r hr => by omega)
    (fun r hr => Nat.sub_le _ _)

lemma shiftCommon_le_pow_two (n : ℕ) :
    shiftCommon n ≤ 2 ^ (triangular n + 3 * n) := by
  rw [shiftCommon, triangular]
  calc
    (∏ h ∈ Finset.range n, (2 ^ (h + 4) - 3)) ≤
        ∏ h ∈ Finset.range n, 2 ^ (h + 4) :=
      Finset.prod_le_prod (fun h hh => by omega) (fun h hh => Nat.sub_le _ _)
    _ = 2 ^ (∑ h ∈ Finset.range n, (h + 4)) :=
      Finset.prod_pow_eq_pow_sum (Finset.range n) (fun h => h + 4) 2
    _ = 2 ^ ((∑ h ∈ Finset.range n, (h + 1)) + 3 * n) := by
      congr 1
      simp only [show ∀ h : ℕ, h + 4 = (h + 1) + 3 by omega,
        Finset.sum_add_distrib]
      simp [Nat.mul_comm]

/-- A power-of-two upper exponent for the common multiplier. -/
def scaleExponent (n : ℕ) : ℕ :=
  2 * n + triangular (n - 1) + triangular (overlapIndex n) +
    triangular n + 3 * n

lemma commonMultiplier_le_pow_two (n : ℕ) :
    commonMultiplier n ≤ 2 ^ scaleExponent n := by
  have h3 : 3 ^ n ≤ 2 ^ (2 * n) := by
    calc
      3 ^ n ≤ 4 ^ n := Nat.pow_le_pow_left (by norm_num) n
      _ = 2 ^ (2 * n) := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, pow_mul]
  have hodd : oddCommon n ≤
      2 ^ triangular (n - 1) * 2 ^ triangular (overlapIndex n) := by
    exact Nat.mul_le_mul (oddProduct_le_pow_two _) (oddProduct_le_pow_two _)
  have hshift := shiftCommon_le_pow_two n
  rw [commonMultiplier, scaleExponent]
  calc
    3 ^ n * oddCommon n * shiftCommon n ≤
        2 ^ (2 * n) *
          (2 ^ triangular (n - 1) * 2 ^ triangular (overlapIndex n)) *
            2 ^ (triangular n + 3 * n) := by
      exact Nat.mul_le_mul (Nat.mul_le_mul h3 hodd) hshift
    _ = 2 ^ (2 * n + triangular (n - 1) + triangular (overlapIndex n) +
          triangular n + 3 * n) := by
      simp only [← pow_add]
      congr 1
      omega

lemma kernelExponent_self (n : ℕ) :
    kernelExponent n n = triangular n + n * n := by
  rw [kernelExponent, triangular]
  simp only [Finset.sum_add_distrib]
  simp

lemma scaleExponent_add_le_kernelExponent (N : ℕ) (hN : 14 ≤ N) :
    scaleExponent (N + 2) + N ≤ kernelExponent (N + 2) (N + 2) := by
  let n := N + 2
  let t := overlapIndex n
  have hn : 16 ≤ n := by omega
  have ht1 : 2 * t ≤ n - 1 := by
    change 2 * ((n - 1) / 2) ≤ n - 1
    omega
  have ht2 : 2 * (t + 1) ≤ n + 1 := by omega
  have htprod : 4 * (t * (t + 1)) ≤ (n - 1) * (n + 1) := by
    nlinarith [Nat.mul_le_mul ht1 ht2]
  have htri1 := triangular_twice (n - 1)
  have htrit := triangular_twice t
  have htrin := triangular_twice n
  rw [scaleExponent, kernelExponent_self]
  change 2 * n + triangular (n - 1) + triangular t + triangular n + 3 * n + N ≤
    triangular n + n * n
  dsimp [n] at *
  nlinarith

lemma abs_linear_form_le_geometric (N : ℕ) (hN : 14 ≤ N) :
    |(linearA N : ℝ) * shiftedValue + (linearB N : ℝ)| ≤
      2 * (1 / 2 : ℝ) ^ N := by
  rw [linear_form_eq_kernelTail, abs_mul]
  rw [abs_of_nonneg (by exact_mod_cast (Nat.zero_le (commonMultiplier (N + 2))))]
  have hM : (commonMultiplier (N + 2) : ℝ) ≤
      (2 : ℝ) ^ scaleExponent (N + 2) := by
    exact_mod_cast commonMultiplier_le_pow_two (N + 2)
  have hF := abs_kernelTail_le N
  calc
    (commonMultiplier (N + 2) : ℝ) * |kernelTail (N + 2)| ≤
        (commonMultiplier (N + 2) : ℝ) *
          (2 / (2 : ℝ) ^ kernelExponent (N + 2) (N + 2)) := by
      gcongr
    _ ≤ (2 : ℝ) ^ scaleExponent (N + 2) *
          (2 / (2 : ℝ) ^ kernelExponent (N + 2) (N + 2)) := by
      gcongr
    _ ≤ 2 * (1 / 2 : ℝ) ^ N := by
      rw [one_div_pow]
      have hpow : (2 : ℝ) ^ (scaleExponent (N + 2) + N) ≤
          (2 : ℝ) ^ kernelExponent (N + 2) (N + 2) :=
        pow_le_pow_right₀ (by norm_num)
          (scaleExponent_add_le_kernelExponent N hN)
      have hden : 0 < (2 : ℝ) ^ kernelExponent (N + 2) (N + 2) := by positivity
      have hNpow : 0 < (2 : ℝ) ^ N := by positivity
      rw [← mul_div_assoc]
      rw [show 2 * (1 / (2 : ℝ) ^ N) = 2 / (2 : ℝ) ^ N by ring]
      rw [div_le_div_iff₀ hden hNpow]
      have hpow' : (2 : ℝ) ^ scaleExponent (N + 2) * (2 : ℝ) ^ N ≤
          (2 : ℝ) ^ kernelExponent (N + 2) (N + 2) := by
        rw [← pow_add]
        exact hpow
      nlinarith

lemma linear_forms_tendsto_zero :
    Filter.Tendsto
      (fun N => (linearA N : ℝ) * shiftedValue + (linearB N : ℝ))
      Filter.atTop (nhds 0) := by
  apply squeeze_zero_norm' (a := fun N => 2 * (1 / 2 : ℝ) ^ N)
  · filter_upwards [Filter.eventually_atTop.2 ⟨14, fun N hN => hN⟩] with N hN
    rw [Real.norm_eq_abs]
    exact abs_linear_form_le_geometric N hN
  · simpa using
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one
        (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).const_mul 2

/-! ## Irrationality -/

theorem shiftedValue_irrational : Irrational shiftedValue := by
  apply Erdos250Scratch.irrational_of_integer_linear_forms_tendsto_zero
    shiftedValue linearA linearB
  · exact Filter.Eventually.of_forall linear_form_ne_zero
  · exact linear_forms_tendsto_zero

/-- Erdős Problem 1050: the series `∑_{n≥1} 1 / (2^n - 3)` is irrational. -/
theorem erdos_1050 : Irrational erdos1050Series := by
  rw [erdos1050Series_eq_one_fifth_sub_shifted]
  have hdiv : Irrational (shiftedValue / ((3 : ℚ) : ℝ)) := by
    rw [irrational_div_ratCast_iff]
    exact ⟨by norm_num, shiftedValue_irrational⟩
  have hout : Irrational (((1 / 5 : ℚ) : ℝ) - shiftedValue / ((3 : ℚ) : ℝ)) := by
    rw [irrational_ratCast_sub_iff]
    exact hdiv
  norm_num at hout ⊢
  exact hout

end

end Erdos1050

#print axioms Erdos1050.erdos_1050
