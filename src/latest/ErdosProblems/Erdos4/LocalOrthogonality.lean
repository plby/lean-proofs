import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Option
import Mathlib.Tactic

/-!
# Exact local orthogonality for one sieve prime

`none` is the unoccupied residue state and `some i` is the state in which
the `i`th affine form vanishes. The occupied states have probability `1 / ell`.
-/

open scoped BigOperators

namespace Erdos4.LocalOrthogonality

noncomputable def coupling (ell : ℝ) (k : ℕ) : ℝ :=
  (Real.sqrt ell + Real.sqrt (ell - k))⁻¹

noncomputable def basis {k : ℕ} (ell : ℝ) (i : Fin k) : Option (Fin k) → ℝ
  | none => (Real.sqrt (ell - k))⁻¹
  | some j => coupling ell k - if j = i then Real.sqrt ell else 0

noncomputable def mean {k : ℕ} (ell : ℝ) (f : Option (Fin k) → ℝ) : ℝ :=
  ((ell - k) / ell) * f none + (1 / ell) * ∑ j : Fin k, f (some j)

noncomputable def stateWeight (ell : ℝ) (k : ℕ) : Option (Fin k) → ℝ
  | none => (ell - k) / ell
  | some _ => 1 / ell

theorem mean_eq_sum {k : ℕ} (ell : ℝ) (f : Option (Fin k) → ℝ) :
    mean ell f = ∑ s, stateWeight ell k s * f s := by
  rw [Fintype.sum_option]
  simp only [stateWeight, mean, Finset.mul_sum]

theorem stateWeight_nonneg {ell : ℝ} {k : ℕ} (h : (k : ℝ) < ell)
    (s : Option (Fin k)) : 0 ≤ stateWeight ell k s := by
  have hell : 0 < ell := lt_of_le_of_lt (Nat.cast_nonneg k) h
  cases s with
  | none => exact div_nonneg (sub_pos.mpr h).le hell.le
  | some _ => exact (one_div_pos.mpr hell).le

theorem sqrt_pos {ell : ℝ} {k : ℕ} (h : (k : ℝ) < ell) : 0 < Real.sqrt ell := by
  exact Real.sqrt_pos.mpr (lt_of_le_of_lt (Nat.cast_nonneg k) h)

theorem complement_sqrt_pos {ell : ℝ} {k : ℕ} (h : (k : ℝ) < ell) :
    0 < Real.sqrt (ell - k) := Real.sqrt_pos.mpr (sub_pos.mpr h)

theorem coupling_mul_card {ell : ℝ} {k : ℕ} (h : (k : ℝ) < ell) :
    (k : ℝ) * coupling ell k = Real.sqrt ell - Real.sqrt (ell - k) := by
  have hu := sqrt_pos h
  have hv := complement_sqrt_pos h
  have hu2 := Real.sq_sqrt (lt_of_le_of_lt (Nat.cast_nonneg k) h).le
  have hv2 := Real.sq_sqrt (sub_pos.mpr h).le
  unfold coupling
  apply (mul_inv_eq_iff_eq_mul₀ (by positivity : Real.sqrt ell + Real.sqrt (ell - k) ≠ 0)).mpr
  nlinarith

theorem coupling_quadratic {ell : ℝ} {k : ℕ} (h : (k : ℝ) < ell) :
    (k : ℝ) * coupling ell k ^ 2 - 2 * coupling ell k * Real.sqrt ell = -1 := by
  have hu := sqrt_pos h
  have hv := complement_sqrt_pos h
  have hsum : coupling ell k * (Real.sqrt ell + Real.sqrt (ell - k)) = 1 := by
    exact inv_mul_cancel₀ (by positivity)
  have hcard := coupling_mul_card h
  nlinarith [congrArg (fun a : ℝ => a * coupling ell k) hcard]

theorem sum_basis {k : ℕ} (ell : ℝ) (i : Fin k) :
    (∑ j : Fin k, basis ell i (some j)) =
      (k : ℝ) * coupling ell k - Real.sqrt ell := by
  simp [basis, Finset.sum_sub_distrib]

theorem sum_basis_mul {k : ℕ} (ell : ℝ) (i h : Fin k) :
    (∑ j : Fin k, basis ell i (some j) * basis ell h (some j)) =
      (k : ℝ) * coupling ell k ^ 2 - 2 * coupling ell k * Real.sqrt ell +
        if i = h then (Real.sqrt ell) ^ 2 else 0 := by
  classical
  have hexpand : ∀ j : Fin k, basis ell i (some j) * basis ell h (some j) =
      coupling ell k ^ 2 - (if j = i then coupling ell k * Real.sqrt ell else 0) -
      (if j = h then coupling ell k * Real.sqrt ell else 0) +
      (if j = i then (if i = h then (Real.sqrt ell) ^ 2 else 0) else 0) := by
    intro j
    by_cases hji : j = i
    · subst j
      by_cases hih : i = h
      · simp [basis, hih]
        ring
      · simp [basis, hih]
        ring
    · by_cases hjh : j = h
      · subst j
        simp [basis, hji]
        ring
      · simp [basis, hji, hjh]
        ring
  simp_rw [hexpand]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp
  ring

theorem mean_one {ell : ℝ} {k : ℕ} (h : (k : ℝ) < ell) :
    mean (k := k) ell (fun _ => 1) = 1 := by
  have hell : ell ≠ 0 := (lt_of_le_of_lt (Nat.cast_nonneg k) h).ne'
  unfold mean
  simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

theorem mean_basis {ell : ℝ} {k : ℕ} (h : (k : ℝ) < ell) (i : Fin k) :
    mean ell (basis ell i) = 0 := by
  have hell := (lt_of_le_of_lt (Nat.cast_nonneg k) h).ne'
  have hv := complement_sqrt_pos h
  have hv2 := Real.sq_sqrt (sub_pos.mpr h).le
  unfold mean
  rw [sum_basis, coupling_mul_card h]
  simp only [basis]
  field_simp
  nlinarith

/-- The centered local basis is exactly orthonormal. -/
theorem mean_basis_mul {ell : ℝ} {k : ℕ} (h : (k : ℝ) < ell) (i j : Fin k) :
    mean ell (fun s => basis ell i s * basis ell j s) = if i = j then 1 else 0 := by
  have hell := (lt_of_le_of_lt (Nat.cast_nonneg k) h).ne'
  have hv := complement_sqrt_pos h
  have hu2 := Real.sq_sqrt (lt_of_le_of_lt (Nat.cast_nonneg k) h).le
  have hv2 := Real.sq_sqrt (sub_pos.mpr h).le
  unfold mean
  rw [sum_basis_mul, coupling_quadratic h]
  simp only [basis]
  by_cases hij : i = j
  · simp only [if_pos hij]
    field_simp
    nlinarith
  · simp only [if_neg hij]
    field_simp
    nlinarith

noncomputable def extendedBasis {k : ℕ} (ell : ℝ) :
    Option (Fin k) → Option (Fin k) → ℝ
  | none => fun _ => 1
  | some i => basis ell i

theorem mean_extendedBasis_mul {ell : ℝ} {k : ℕ} (h : (k : ℝ) < ell)
    (a b : Option (Fin k)) :
    mean ell (fun s => extendedBasis ell a s * extendedBasis ell b s) =
      if a = b then 1 else 0 := by
  cases a with
  | none =>
    cases b with
    | none => simpa only [extendedBasis, mul_one, ↓reduceIte] using mean_one h
    | some j => simpa only [extendedBasis, one_mul, reduceCtorEq, ↓reduceIte] using mean_basis h j
  | some i =>
    cases b with
    | none => simpa only [extendedBasis, mul_one, reduceCtorEq, ↓reduceIte] using mean_basis h i
    | some j => simpa only [extendedBasis, Option.some.injEq] using mean_basis_mul h i j

theorem mean_sum {k : ℕ} {α : Type*} (ell : ℝ) (S : Finset α)
    (f : α → Option (Fin k) → ℝ) :
    mean ell (fun s => ∑ a ∈ S, f a s) = ∑ a ∈ S, mean ell (f a) := by
  unfold mean
  simp only [Finset.mul_sum, Finset.sum_add_distrib]
  rw [Finset.sum_comm]

theorem mean_const_mul {k : ℕ} (ell c : ℝ) (f : Option (Fin k) → ℝ) :
    mean ell (fun s => c * f s) = c * mean ell f := by
  unfold mean
  rw [← Finset.mul_sum]
  ring

/-- Exact one-prime Parseval identity for the coefficient coordinates. -/
theorem mean_expansion_mul {ell : ℝ} {k : ℕ} (h : (k : ℝ) < ell)
    (v w : Option (Fin k) → ℝ) :
    mean ell (fun s => (∑ a, v a * extendedBasis ell a s) *
      (∑ b, w b * extendedBasis ell b s)) = ∑ a, v a * w a := by
  classical
  have heq : ∀ s : Option (Fin k),
      (∑ a, v a * extendedBasis ell a s) * (∑ b, w b * extendedBasis ell b s) =
        ∑ a, ∑ b, (v a * w b) * (extendedBasis ell a s * extendedBasis ell b s) := by
    intro s
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _ha
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _hb
    ring
  simp_rw [heq]
  rw [mean_sum]
  simp_rw [mean_sum, mean_const_mul, mean_extendedBasis_mul h]
  simp

theorem mean_expansion_sq {ell : ℝ} {k : ℕ} (h : (k : ℝ) < ell)
    (v : Option (Fin k) → ℝ) :
    mean ell (fun s => (∑ a, v a * extendedBasis ell a s) ^ 2) = ∑ a, v a ^ 2 := by
  simpa only [pow_two] using mean_expansion_mul h v v

theorem basis_occupied_symm {k : ℕ} (ell : ℝ) (i j : Fin k) :
    basis ell i (some j) = basis ell j (some i) := by
  simp only [basis, eq_comm]

/-- The normalized evaluation vector at an occupied state has norm one. -/
theorem sum_evaluation_sq {ell : ℝ} {k : ℕ} (h : (k : ℝ) < ell) (j : Fin k) :
    (∑ a : Option (Fin k), extendedBasis ell a (some j) ^ 2) = ell := by
  have hu2 := Real.sq_sqrt (lt_of_le_of_lt (Nat.cast_nonneg k) h).le
  rw [Fintype.sum_option]
  simp only [extendedBasis, one_pow]
  simp_rw [basis_occupied_symm ell _ j, pow_two]
  rw [sum_basis_mul, coupling_quadratic h]
  simp only [↓reduceIte]
  nlinarith

noncomputable def conditionalMean {k : ℕ} (ell : ℝ) (j : Fin k)
    (f : Option (Fin k) → ℝ) : ℝ :=
  (((ell - k) / ell) * f none +
    (1 / ell) * ∑ i ∈ Finset.univ.erase j, f (some i)) / (1 - 1 / ell)

theorem conditionalMean_eq {k : ℕ} (ell : ℝ) (j : Fin k)
    (f : Option (Fin k) → ℝ) :
    conditionalMean ell j f = (mean ell f - f (some j) / ell) / (1 - 1 / ell) := by
  unfold conditionalMean mean
  congr 1
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
  ring

theorem conditionalMean_nonneg {ell : ℝ} {k : ℕ} (h : (k : ℝ) < ell)
    (j : Fin k) (f : Option (Fin k) → ℝ) (hf : ∀ s, 0 ≤ f s) :
    0 ≤ conditionalMean ell j f := by
  have hk : 1 ≤ k := by have := j.isLt; omega
  have hell : 1 < ell := lt_of_le_of_lt (by exact_mod_cast hk) h
  have hellpos : 0 < ell := lt_trans zero_lt_one hell
  have hinv : 1 / ell < 1 := (div_lt_one hellpos).mpr hell
  unfold conditionalMean
  exact div_nonneg
    (add_nonneg (mul_nonneg (div_nonneg (sub_pos.mpr h).le hellpos.le) (hf none))
      (mul_nonneg (one_div_pos.mpr hellpos).le (Finset.sum_nonneg (fun i _hi => hf (some i)))))
    (sub_pos.mpr hinv).le

theorem conditionalMean_one {ell : ℝ} {k : ℕ} (h : (k : ℝ) < ell) (j : Fin k) :
    conditionalMean ell j (fun _ => 1) = 1 := by
  have hk : 1 ≤ k := by have := j.isLt; omega
  have hell : 1 < ell := lt_of_le_of_lt (by exact_mod_cast hk) h
  have hellpos : 0 < ell := lt_trans zero_lt_one hell
  have hinv : 1 / ell < 1 := (div_lt_one hellpos).mpr hell
  rw [conditionalMean_eq, mean_one h]
  exact div_self (sub_pos.mpr hinv).ne'

/-- Exact rank-one deletion in the local Gram form. -/
theorem conditionalMean_expansion_sq {ell : ℝ} {k : ℕ} (h : (k : ℝ) < ell)
    (j : Fin k) (v : Option (Fin k) → ℝ) :
    conditionalMean ell j (fun s => (∑ a, v a * extendedBasis ell a s) ^ 2) =
      ((∑ a, v a ^ 2) - (∑ a, v a * extendedBasis ell a (some j)) ^ 2 / ell) /
        (1 - 1 / ell) := by
  rw [conditionalMean_eq, mean_expansion_sq h]

end Erdos4.LocalOrthogonality
