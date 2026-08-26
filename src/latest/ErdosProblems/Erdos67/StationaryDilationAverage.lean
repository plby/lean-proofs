import ErdosProblems.Erdos67.StationaryConcentration
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Elementary multiplicative averaging boxes

The generators are the integers `1,…,t`, rather than primes. A fixed positive
dilation is one generator once the box is large enough. Rotating its exponent
coordinate preserves the uniform law and changes multiplication only on a face
of relative size `1/t`.
-/

open scoped BigOperators
open Finset

namespace Erdos67.FiniteEntropy

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

theorem piVector_expectation_coordinate (q : FinProb α) (i : ι) (F : α → ℝ) :
    (∑ y : ι → α, piVector (fun _ : ι ↦ q) y * F (y i)) = ∑ a, q a * F a := by
  classical
  have h := piVector_expectation_prod (fun _ : ι ↦ q)
    (fun j a ↦ if j = i then F a else 1)
  have hprod (y : ι → α) : (∏ j, if j = i then F (y j) else 1) = F (y i) := by
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hji
      simp [hji]
    · simp
  simp_rw [hprod] at h
  rw [Finset.prod_eq_single i] at h
  · simpa only [if_true] using h
  · intro j _ hji
    simp only [hji, if_false, mul_one, stdSimplex.sum_eq_one]
  · simp

theorem uniform_expectation_comp_perm [Nonempty α] (e : Equiv.Perm α) (F : α → ℝ) :
    (∑ a, uniformVector a * F (e a)) = ∑ a, uniformVector a * F a := by
  change (∑ a, (Fintype.card α : ℝ)⁻¹ * F (e a)) =
    ∑ a, (Fintype.card α : ℝ)⁻¹ * F a
  rw [← Finset.mul_sum, ← Finset.mul_sum, Equiv.sum_comp e]

theorem uniform_coordinate_probability [Nonempty α] [DecidableEq α] (i : ι) (a : α) :
    (∑ y : ι → α, uniformVector y * if y i = a then (1 : ℝ) else 0) =
      (Fintype.card α : ℝ)⁻¹ := by
  have h := piVector_expectation_coordinate (uniformVector (α := α)) i
    (fun b ↦ if b = a then (1 : ℝ) else 0)
  rw [piVector_uniform] at h
  simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, uniformVector_apply] using h

end Erdos67.FiniteEntropy

namespace Erdos67.StationaryDilationAverage

variable {t : ℕ}

/-- A finite multiplicative box, allowing repeated representations of an integer. -/
def boxValue (a : Fin t → Fin t) : ℕ := ∏ i, (i.val + 1) ^ (a i).val

theorem boxValue_pos (a : Fin t → Fin t) : 0 < boxValue a := by
  exact Finset.prod_pos fun i _ ↦ pow_pos (Nat.succ_pos _) _

/-- Rotate a single exponent coordinate cyclically. -/
def rotateCoordinate (i : Fin t) : Equiv.Perm (Fin t → Fin t) where
  toFun a := fun j ↦ if j = i then finRotate t (a j) else a j
  invFun a := fun j ↦ if j = i then (finRotate t).symm (a j) else a j
  left_inv a := by
    funext j
    by_cases hj : j = i
    · simp only [hj, if_true, Equiv.symm_apply_apply]
    · simp only [hj, if_false]
  right_inv a := by
    funext j
    by_cases hj : j = i
    · simp only [hj, if_true, Equiv.apply_symm_apply]
    · simp only [hj, if_false]

theorem boxValue_rotateCoordinate (i : Fin (t + 1)) (a : Fin (t + 1) → Fin (t + 1))
    (ha : a i ≠ Fin.last t) :
    boxValue (rotateCoordinate i a) = (i.val + 1) * boxValue a := by
  have hfactor (j : Fin (t + 1)) :
      (j.val + 1) ^ (rotateCoordinate i a j).val =
        (if j = i then i.val + 1 else 1) * (j.val + 1) ^ (a j).val := by
    by_cases hj : j = i
    · subst j
      change (i.val + 1) ^ (if i = i then finRotate (t + 1) (a i) else a i).val = _
      rw [if_pos rfl, if_pos rfl, coe_finRotate_of_ne_last ha, pow_succ']
    · simp [rotateCoordinate, hj]
  unfold boxValue
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib]
  congr 1
  simp

/-- The boundary face on which rotation wraps around has mass exactly `1/t`. -/
theorem uniform_boundary_probability (i : Fin (t + 1)) :
    (∑ a : Fin (t + 1) → Fin (t + 1), FiniteEntropy.uniformVector a *
      if a i = Fin.last t then (1 : ℝ) else 0) = ((t + 1 : ℕ) : ℝ)⁻¹ := by
  simpa only [Fintype.card_fin] using
    FiniteEntropy.uniform_coordinate_probability i (Fin.last t)

/-- Averaging over the box is approximately invariant under each generator,
uniformly over all real observables bounded by `B`. -/
theorem abs_uniform_dilation_sub_le (i : Fin (t + 1)) (F : ℕ → ℝ) (B : ℝ)
    (hF : ∀ n, |F n| ≤ B) :
    |(∑ a : Fin (t + 1) → Fin (t + 1), FiniteEntropy.uniformVector a *
        F ((i.val + 1) * boxValue a)) -
      ∑ a : Fin (t + 1) → Fin (t + 1), FiniteEntropy.uniformVector a * F (boxValue a)| ≤
        2 * B / (t + 1 : ℕ) := by
  have hperm := FiniteEntropy.uniform_expectation_comp_perm (rotateCoordinate i)
    (fun a ↦ F (boxValue a))
  rw [← hperm, ← Finset.sum_sub_distrib]
  have hpoint (a : Fin (t + 1) → Fin (t + 1)) :
      |F ((i.val + 1) * boxValue a) - F (boxValue (rotateCoordinate i a))| ≤
        (if a i = Fin.last t then (1 : ℝ) else 0) * (2 * B) := by
    by_cases ha : a i = Fin.last t
    · rw [if_pos ha, one_mul]
      have h := abs_sub (F ((i.val + 1) * boxValue a)) (F (boxValue (rotateCoordinate i a)))
      linarith [hF ((i.val + 1) * boxValue a), hF (boxValue (rotateCoordinate i a))]
    · rw [if_neg ha, zero_mul, boxValue_rotateCoordinate i a ha, sub_self, abs_zero]
  calc
    |∑ a : Fin (t + 1) → Fin (t + 1),
        (FiniteEntropy.uniformVector a * F ((i.val + 1) * boxValue a) -
          FiniteEntropy.uniformVector a * F (boxValue (rotateCoordinate i a)))| ≤
        ∑ a : Fin (t + 1) → Fin (t + 1), FiniteEntropy.uniformVector a *
          ((if a i = Fin.last t then (1 : ℝ) else 0) * (2 * B)) := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro a _
      rw [← mul_sub, abs_mul, abs_of_nonneg (FiniteEntropy.prob_nonneg _ a)]
      exact mul_le_mul_of_nonneg_left (hpoint a) (FiniteEntropy.prob_nonneg _ a)
    _ = 2 * B / (t + 1 : ℕ) := by
      simp_rw [← mul_assoc]
      rw [← Finset.sum_mul, ← Finset.sum_mul, uniform_boundary_probability]
      ring

end Erdos67.StationaryDilationAverage
