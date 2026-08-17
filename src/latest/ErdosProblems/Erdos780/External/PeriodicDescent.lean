import Mathlib

/-!
The algebraic downward step in the periodic-resolution proof.  All degrees
may live in one ambient chain module; homogeneity is needed only to establish
that the chosen top chain is zero.
-/

namespace PeriodicDescent

variable {A : Type*} [AddCommGroup A]

structure Datum (A : Type*) [AddCommGroup A] where
  boundary : A →+ A
  tau : A →+ A
  normOp : A →+ A
  boundary_sq : ∀ x, boundary (boundary x) = 0
  boundary_tau : ∀ x, boundary (tau x) = tau (boundary x)
  boundary_norm : ∀ x, boundary (normOp x) = normOp (boundary x)
  ker_tau : ∀ {x}, tau x = 0 → ∃ y, normOp y = x
  ker_norm : ∀ {x}, normOp x = 0 → ∃ y, tau y = x

namespace Datum

variable (P : Datum A)

def op (i : ℕ) : A →+ A := if Odd i then P.tau else P.normOp

@[simp] theorem op_zero : P.op 0 = P.normOp := by simp [op]

theorem boundary_op (i : ℕ) (x : A) :
    P.boundary (P.op i x) = P.op i (P.boundary x) := by
  by_cases hi : Odd i
  · simp [op, hi, P.boundary_tau]
  · simp [op, hi, P.boundary_norm]

theorem exact_op_succ (i : ℕ) {x : A} (hx : P.op (i + 1) x = 0) :
    ∃ y, P.op i y = x := by
  rcases Nat.even_or_odd i with hi | hi
  · have hni : ¬ Odd i := Nat.not_odd_iff_even.mpr hi
    have his : Odd (i + 1) := hi.add_one
    simpa [op, hni] using P.ker_tau (by simpa [op, his] using hx)
  · have his : ¬ Odd (i + 1) := Nat.not_odd_iff_even.mpr hi.add_one
    simpa [op, hi] using P.ker_norm (by simpa [op, his] using hx)

/-- Starting from a decomposition in degree `i`, descend to degree zero.
The `next` argument is the degree-`i+1` correction and `same` is the
degree-`i` correction.
-/
theorem descend_from
    (y : ℕ → A)
    (hrel : ∀ i, P.boundary (y (i + 1)) = P.op (i + 1) (y i)) :
    ∀ (i : ℕ) (next same : A),
      y i = P.boundary next + P.op i same →
      ∃ z₁ z₀ : A, y 0 = P.boundary z₁ + P.normOp z₀ := by
  intro i
  induction i with
  | zero =>
      intro next same h
      exact ⟨next, same, by simpa using h⟩
  | succ i ih =>
      intro next same h
      have hk : P.op (i + 1) (y i - P.boundary same) = 0 := by
        rw [map_sub, ← hrel i]
        have hb := congrArg P.boundary h
        simp only [map_add, P.boundary_op, P.boundary_sq, zero_add] at hb
        exact sub_eq_zero.mpr hb
      obtain ⟨previous, hp⟩ := P.exact_op_succ i hk
      apply ih same previous
      rw [hp]
      abel

/-- If a resolution chain has zero top component, its bottom component is a
boundary plus a norm. -/
theorem bottom_decomposition
    (y : ℕ → A)
    (hrel : ∀ i, P.boundary (y (i + 1)) = P.op (i + 1) (y i))
    (Q : ℕ) (htop : y Q = 0) :
    ∃ z₁ z₀ : A, y 0 = P.boundary z₁ + P.normOp z₀ := by
  apply P.descend_from y hrel Q 0 0
  simp [htop]

end Datum
end PeriodicDescent
