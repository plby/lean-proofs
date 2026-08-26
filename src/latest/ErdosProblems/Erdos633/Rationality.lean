import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Rational real numbers in the necessity arguments

The rational subfield is used for the algebraic consequences of boundary
invariants. These lemmas do not assume that an arbitrary tiling supplies
the boundary equations; extracting them from geometry is a separate step.
-/

namespace Erdos633

noncomputable def rationalReals : Subfield ℝ := (Rat.castHom ℝ).fieldRange

theorem mem_rationalReals_iff (x : ℝ) :
    x ∈ rationalReals ↔ ∃ q : ℚ, (q : ℝ) = x := Iff.rfl

@[simp] theorem rationalReals_rat (q : ℚ) : (q : ℝ) ∈ rationalReals := ⟨q, rfl⟩

@[simp] theorem rationalReals_int (m : ℤ) : (m : ℝ) ∈ rationalReals :=
  ⟨m, by simp⟩

@[simp] theorem rationalReals_nat (m : ℕ) : (m : ℝ) ∈ rationalReals :=
  ⟨m, by simp⟩

/-- A nonzero rational coefficient can be cancelled in a rational product. -/
theorem rational_of_mul {a x : ℝ} (ha : a ∈ rationalReals) (ha0 : a ≠ 0)
    (hax : a * x ∈ rationalReals) : x ∈ rationalReals := by
  have h := rationalReals.div_mem hax ha
  simpa [ha0] using h

/-- Uniqueness of coefficients of an irrational real over the rational subfield. -/
theorem rational_coefficients_eq {x u v : ℝ} (hx : x ∉ rationalReals)
    (hu : u ∈ rationalReals) (hv : v ∈ rationalReals) (h : u * x = v) : u = 0 := by
  by_contra hu0
  exact hx (rational_of_mul hu hu0 (h ▸ hv))

/-- A boundary side in `ℚ * x` cannot contain a strictly positive rational
contribution unless `x` is rational. -/
theorem rational_of_positive_boundary {x t r : ℝ}
    (ht : t ∈ rationalReals) (hr : r ∈ rationalReals) (hrpos : 0 < r)
    (h : t * x = r) : x ∈ rationalReals := by
  have ht0 : t ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at h
    linarith
  exact rational_of_mul ht ht0 (h ▸ hr)

/-- Two boundary decompositions with opposite irrational coefficients cannot
both have nonnegative coefficients unless that coefficient vanishes. -/
theorem opposite_boundary_coefficients {x t u v : ℝ}
    (hx : x ∉ rationalReals) (ht : t ∈ rationalReals)
    (hu : u ∈ rationalReals) (hv : v ∈ rationalReals)
    (p q : ℕ) (hp : t * x = (p : ℝ) * x + u)
    (hq : -t * x = (q : ℝ) * x + v) : t = 0 := by
  have hp' : t - p = 0 := rational_coefficients_eq hx
    (rationalReals.sub_mem ht (rationalReals_nat p)) hu (by linarith only [hp])
  have hq' : -t - q = 0 := rational_coefficients_eq hx
    (rationalReals.sub_mem (rationalReals.neg_mem ht) (rationalReals_nat q)) hv
    (by linarith only [hq])
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  linarith only [hp', hq', hp0, hq0]

end Erdos633
