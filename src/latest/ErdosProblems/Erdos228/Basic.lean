/-
Foundational definitions and elementary polynomial lemmas for Erdős Problem 228.

This file contains no analytic input from the flat-polynomial construction.  It
packages finite coefficient vectors as polynomials, records the elementary
monomial-shift identities, and converts positive non-strict flatness constants
to the strict inequalities used by the formal statement.
-/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

namespace Erdos228

open Filter

/-! ### Littlewood polynomials -/

/-- A complex number is a sign when it is either `1` or `-1`. -/
def IsSign (a : ℂ) : Prop := a = 1 ∨ a = -1

theorem IsSign.ne_zero {a : ℂ} (ha : IsSign a) : a ≠ 0 := by
  rcases ha with rfl | rfl <;> norm_num

theorem IsSign.norm_eq_one {a : ℂ} (ha : IsSign a) : ‖a‖ = 1 := by
  rcases ha with rfl | rfl <;> simp

/-- The coefficient and degree conditions in the statement of Erdős 228. -/
def IsLittlewood (n : ℕ) (p : Polynomial ℂ) : Prop :=
  p.degree = n ∧ ∀ i ≤ n, IsSign (p.coeff i)

/-- Build a polynomial from a coefficient vector indexed by `0, ..., n`. -/
noncomputable def ofCoeffs (n : ℕ) (a : Fin (n + 1) → ℂ) : Polynomial ℂ :=
  ∑ i : Fin (n + 1), Polynomial.monomial (i : ℕ) (a i)

theorem coeff_ofCoeffs_of_le (n i : ℕ) (a : Fin (n + 1) → ℂ) (hi : i ≤ n) :
    (ofCoeffs n a).coeff i = a ⟨i, Nat.lt_succ_iff.mpr hi⟩ := by
  classical
  change Polynomial.lcoeff ℂ i
      (∑ j : Fin (n + 1), Polynomial.monomial (j : ℕ) (a j)) = _
  rw [map_sum]
  rw [Finset.sum_eq_single ⟨i, Nat.lt_succ_iff.mpr hi⟩]
  · simp
  · intro j _ hj
    simp only [Polynomial.lcoeff_apply, Polynomial.coeff_monomial]
    rw [if_neg]
    intro hji
    apply hj
    exact Fin.ext hji
  · simp

theorem coeff_ofCoeffs_of_lt (n i : ℕ) (a : Fin (n + 1) → ℂ) (hi : n < i) :
    (ofCoeffs n a).coeff i = 0 := by
  classical
  change Polynomial.lcoeff ℂ i
      (∑ j : Fin (n + 1), Polynomial.monomial (j : ℕ) (a j)) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro j _
  simp only [Polynomial.lcoeff_apply, Polynomial.coeff_monomial]
  rw [if_neg]
  exact ne_of_lt ((Nat.le_of_lt_succ j.isLt).trans_lt hi)

theorem eval_ofCoeffs (n : ℕ) (a : Fin (n + 1) → ℂ) (z : ℂ) :
    (ofCoeffs n a).eval z = ∑ i, a i * z ^ (i : ℕ) := by
  classical
  simpa [ofCoeffs] using Polynomial.eval_finsetSum (Finset.univ : Finset (Fin (n + 1)))
    (fun i : Fin (n + 1) ↦ Polynomial.monomial (i : ℕ) (a i)) z

theorem degree_ofCoeffs (n : ℕ) (a : Fin (n + 1) → ℂ) (ha : a ⟨n, Nat.lt_succ_self n⟩ ≠ 0) :
    (ofCoeffs n a).degree = n := by
  apply Polynomial.degree_eq_of_le_of_coeff_ne_zero
  · rw [Polynomial.degree_le_iff_coeff_zero]
    intro m hm
    exact coeff_ofCoeffs_of_lt n m a (by exact_mod_cast hm)
  · simpa [coeff_ofCoeffs_of_le n n a le_rfl] using ha

/-- A coefficient vector whose entries are all signs produces a Littlewood
polynomial of the indicated degree. -/
theorem isLittlewood_ofCoeffs (n : ℕ) (a : Fin (n + 1) → ℂ)
    (ha : ∀ i, IsSign (a i)) : IsLittlewood n (ofCoeffs n a) := by
  constructor
  · apply degree_ofCoeffs
    rcases ha ⟨n, Nat.lt_succ_self n⟩ with h | h <;> simp [h]
  · intro i hi
    rw [coeff_ofCoeffs_of_le n i a hi]
    exact ha ⟨i, Nat.lt_succ_iff.mpr hi⟩

theorem IsLittlewood.coeff_eq_zero_of_lt {n : ℕ} {p : Polynomial ℂ}
    (hp : IsLittlewood n p) {i : ℕ} (hi : n < i) : p.coeff i = 0 := by
  apply Polynomial.coeff_eq_zero_of_degree_lt
  rw [hp.1]
  exact_mod_cast hi

theorem IsLittlewood.leadingCoeff_isSign {n : ℕ} {p : Polynomial ℂ}
    (hp : IsLittlewood n p) : IsSign p.leadingCoeff := by
  rw [Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_degree_eq_some hp.1]
  exact hp.2 n le_rfl

theorem IsLittlewood.ne_zero {n : ℕ} {p : Polynomial ℂ}
    (hp : IsLittlewood n p) : p ≠ 0 := by
  rw [← Polynomial.degree_ne_bot, hp.1]
  simp

/-! ### Multiplication by a monomial -/

/-- Shift every exponent upward by `k`. -/
noncomputable def shift (k : ℕ) (p : Polynomial ℂ) : Polynomial ℂ :=
  Polynomial.X ^ k * p

theorem coeff_shift (k i : ℕ) (p : Polynomial ℂ) :
    (shift k p).coeff i = if k ≤ i then p.coeff (i - k) else 0 := by
  simpa [shift] using Polynomial.coeff_X_pow_mul' p k i

theorem eval_shift (k : ℕ) (p : Polynomial ℂ) (z : ℂ) :
    (shift k p).eval z = z ^ k * p.eval z := by
  simp [shift]

theorem norm_eval_shift_of_norm_eq_one (k : ℕ) (p : Polynomial ℂ) {z : ℂ}
    (hz : ‖z‖ = 1) : ‖(shift k p).eval z‖ = ‖p.eval z‖ := by
  rw [eval_shift, norm_mul, norm_pow, hz, one_pow, one_mul]

theorem degree_shift {k : ℕ} {p : Polynomial ℂ} :
    (shift k p).degree = p.degree + k := by
  simp [shift, Polynomial.degree_mul, add_comm]

theorem degree_shift_eq {k n : ℕ} {p : Polynomial ℂ} (hp : p.degree = n) :
    (shift k p).degree = n + k := by
  rw [degree_shift, hp]

/-! ### Strictifying uniform square-root bounds -/

/-- The non-strict conclusion furnished by the published theorem. -/
def HasFlatBounds (delta Delta : ℝ) (n : ℕ) (p : Polynomial ℂ) : Prop :=
  ∀ z : ℂ, ‖z‖ = 1 →
    delta * Real.sqrt n ≤ ‖p.eval z‖ ∧ ‖p.eval z‖ ≤ Delta * Real.sqrt n

/-- The strict inequalities in the formal statement. -/
def HasStrictTargetBounds (c₁ c₂ : ℝ) (n : ℕ) (p : Polynomial ℂ) : Prop :=
  ∀ z : ℂ, ‖z‖ = 1 →
    Real.sqrt n < c₁ * ‖p.eval z‖ ∧
      ‖p.eval z‖ < c₂ * Real.sqrt n

theorem HasFlatBounds.shift {delta Delta : ℝ} {n k : ℕ} {p : Polynomial ℂ}
    (hp : HasFlatBounds delta Delta n p) : HasFlatBounds delta Delta n (shift k p) := by
  intro z hz
  simpa [norm_eval_shift_of_norm_eq_one k p hz] using hp z hz

theorem HasStrictTargetBounds.shift {c₁ c₂ : ℝ} {n k : ℕ} {p : Polynomial ℂ}
    (hp : HasStrictTargetBounds c₁ c₂ n p) :
    HasStrictTargetBounds c₁ c₂ n (shift k p) := by
  intro z hz
  simpa [norm_eval_shift_of_norm_eq_one k p hz] using hp z hz

theorem hasStrictTargetBounds_of_hasFlatBounds {delta Delta : ℝ} {n : ℕ}
    {p : Polynomial ℂ} (hdelta : 0 < delta) (hDelta : 0 < Delta) (hn : 0 < n)
    (hp : HasFlatBounds delta Delta n p) :
    HasStrictTargetBounds (2 / delta) (2 * Delta) n p := by
  intro z hz
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  obtain ⟨hlower, hupper⟩ := hp z hz
  constructor
  · have hmul : 2 * Real.sqrt n ≤ (2 / delta) * ‖p.eval z‖ := by
      calc
        2 * Real.sqrt n = (2 / delta) * (delta * Real.sqrt n) := by field_simp
        _ ≤ (2 / delta) * ‖p.eval z‖ :=
          mul_le_mul_of_nonneg_left hlower (by positivity)
    linarith
  · have hstrict : Delta * Real.sqrt n < (2 * Delta) * Real.sqrt n := by
      have := mul_pos hDelta hsqrt
      nlinarith
    exact hupper.trans_lt hstrict

/-- An eventual family with positive non-strict constants supplies the exact
eventual strict statement used by Erdős 228. -/
theorem eventually_strict_of_eventually_flat {delta Delta : ℝ}
    (hdelta : 0 < delta) (hDelta : 0 < Delta)
    (hflat : ∀ᶠ n : ℕ in atTop, ∃ p : Polynomial ℂ,
      IsLittlewood n p ∧ HasFlatBounds delta Delta n p) :
    ∀ᶠ n : ℕ in atTop, ∃ p : Polynomial ℂ,
      p.degree = n ∧
      (∀ i ≤ n, p.coeff i = 1 ∨ p.coeff i = -1) ∧
      HasStrictTargetBounds (2 / delta) (2 * Delta) n p := by
  filter_upwards [hflat, eventually_gt_atTop (0 : ℕ)] with n hnflat hn
  obtain ⟨p, hpLittlewood, hpFlat⟩ := hnflat
  exact ⟨p, hpLittlewood.1, hpLittlewood.2,
    hasStrictTargetBounds_of_hasFlatBounds hdelta hDelta hn hpFlat⟩

end Erdos228
