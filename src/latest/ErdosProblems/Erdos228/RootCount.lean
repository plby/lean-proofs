import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Complex.Basic

namespace Erdos228

/-!
# Root counting for finite Laurent polynomials

The frequency range `[-m,m]` is indexed by `Fin (2 * m + 1)`: index `j`
represents exponent `j - m`.  Multiplication by `z^m` turns the Laurent
polynomial into an ordinary polynomial of degree at most `2 * m`.  This file
records the resulting root bound in a form that can be applied to level sets
of real trigonometric polynomials.
-/

/-- Evaluation of a Laurent polynomial supported on the frequencies
`-m, ..., m`.  Index `j` represents frequency `j - m`. -/
noncomputable def laurentEval (m : ℕ) (a : Fin (2 * m + 1) → ℂ) (z : ℂ) : ℂ :=
  ∑ j, a j * z ^ ((j : ℤ) - (m : ℤ))

/-- The ordinary polynomial obtained from a Laurent polynomial after
multiplication by `z^m`, with the value `w` subtracted. -/
noncomputable def shiftedLevelPolynomial (m : ℕ) (a : Fin (2 * m + 1) → ℂ)
    (w : ℂ) : Polynomial ℂ :=
  (∑ j : Fin (2 * m + 1), Polynomial.monomial (j : ℕ) (a j)) -
    Polynomial.monomial m w

/-- Multiplication by `z^m` clears every negative exponent. -/
theorem eval_shiftedLevelPolynomial (m : ℕ) (a : Fin (2 * m + 1) → ℂ)
    (w z : ℂ) (hz : z ≠ 0) :
    (shiftedLevelPolynomial m a w).eval z = z ^ m * (laurentEval m a z - w) := by
  classical
  simp only [shiftedLevelPolynomial, laurentEval, Polynomial.eval_sub,
    Polynomial.eval_finsetSum, Polynomial.eval_monomial, mul_sub]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hpow : z ^ m * z ^ ((j : ℤ) - (m : ℤ)) = z ^ (j : ℕ) := by
      calc
        z ^ m * z ^ ((j : ℤ) - (m : ℤ)) =
            z ^ (m : ℤ) * z ^ ((j : ℤ) - (m : ℤ)) := by
              rw [zpow_natCast]
        _ = z ^ ((m : ℤ) + ((j : ℤ) - (m : ℤ))) := by
              rw [zpow_add₀ hz]
        _ = z ^ (j : ℤ) := by
              congr 1
              simp [sub_eq_add_neg]
        _ = z ^ (j : ℕ) := by rw [zpow_natCast]
    calc
      a j * z ^ (j : ℕ) =
          a j * (z ^ m * z ^ ((j : ℤ) - (m : ℤ))) := by rw [hpow]
      _ = z ^ m * (a j * z ^ ((j : ℤ) - (m : ℤ))) := by
            simp only [mul_left_comm]
  · simp only [mul_comm]

/-- Clearing negative exponents produces a polynomial of degree at most twice
the frequency bound. -/
theorem natDegree_shiftedLevelPolynomial_le (m : ℕ)
    (a : Fin (2 * m + 1) → ℂ) (w : ℂ) :
    (shiftedLevelPolynomial m a w).natDegree ≤ 2 * m := by
  classical
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro j hj
    apply (Polynomial.natDegree_monomial_le (a j)).trans
    exact Nat.le_of_lt_succ (by simpa [Nat.succ_eq_add_one] using j.isLt)
  · apply (Polynomial.natDegree_monomial_le w).trans
    exact (Nat.le_add_right m m) |>.trans_eq (two_mul m).symm

/-- A nonzero Laurent polynomial with frequencies in `[-m,m]` assumes a
fixed value at no more than `2m` distinct nonzero complex points.  The
nonzero hypothesis is stated for the shifted ordinary polynomial: it is
exactly the exclusion of the identically-constant level case. -/
theorem card_laurent_level_le_twice_frequency (m : ℕ)
    (a : Fin (2 * m + 1) → ℂ) (w : ℂ) (s : Finset ℂ)
    (hp : shiftedLevelPolynomial m a w ≠ 0)
    (hs0 : ∀ z ∈ s, z ≠ 0)
    (hs : ∀ z ∈ s, laurentEval m a z = w) :
    s.card ≤ 2 * m := by
  classical
  calc
    s.card ≤ (shiftedLevelPolynomial m a w).roots.toFinset.card := by
      apply Finset.card_le_card
      intro z hz
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hp, Polynomial.IsRoot.def]
      rw [eval_shiftedLevelPolynomial m a w z (hs0 z hz), hs z hz, sub_self, mul_zero]
    _ ≤ (shiftedLevelPolynomial m a w).roots.card := Multiset.toFinset_card_le _
    _ ≤ (shiftedLevelPolynomial m a w).natDegree := Polynomial.card_roots' _
    _ ≤ 2 * m := natDegree_shiftedLevelPolynomial_le m a w

/-- Parameterized form of the root bound.  It is convenient for trigonometric
level sets: `u` is the parametrization of the unit circle and injectivity is
needed only on the finite set of contacts being counted. -/
theorem card_parameter_laurent_level_le_twice_frequency
    {α : Type*} [DecidableEq α] (m : ℕ)
    (a : Fin (2 * m + 1) → ℂ) (w : ℂ) (u : α → ℂ) (s : Finset α)
    (hp : shiftedLevelPolynomial m a w ≠ 0)
    (hu0 : ∀ x ∈ s, u x ≠ 0)
    (hu_inj : ∀ x ∈ s, ∀ y ∈ s, u x = u y → x = y)
    (hs : ∀ x ∈ s, laurentEval m a (u x) = w) :
    s.card ≤ 2 * m := by
  classical
  have hcard : (s.image u).card = s.card := by
    rw [Finset.card_image_iff]
    exact hu_inj
  rw [← hcard]
  apply card_laurent_level_le_twice_frequency m a w (s.image u) hp
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact hu0 x hx
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact hs x hx

/-- On any half-open interval of length at most `2π`, the usual circle
parametrization is injective; hence a Laurent level has at most `2m` contacts
there. -/
theorem card_angle_laurent_level_le_twice_frequency (m : ℕ)
    (a : Fin (2 * m + 1) → ℂ) (w : ℂ) (s : Finset ℝ) (c d : ℝ)
    (hp : shiftedLevelPolynomial m a w ≠ 0)
    (hcd : d - c ≤ 2 * Real.pi)
    (hscd : ∀ x ∈ s, x ∈ Set.Ico c d)
    (hs : ∀ x ∈ s, laurentEval m a (Circle.exp x : ℂ) = w) :
    s.card ≤ 2 * m := by
  apply card_parameter_laurent_level_le_twice_frequency m a w
    (fun x : ℝ ↦ (Circle.exp x : ℂ)) s hp
  · intro x hx
    exact Circle.coe_ne_zero (Circle.exp x)
  · intro x hx y hy hxy
    apply Circle.exp_injOn_Ico hcd (hscd x hx) (hscd y hy)
    exact Subtype.ext hxy
  · exact hs

/-- The actual level-contact set on a half-open interval. -/
def angleLaurentLevelSet (m : ℕ) (a : Fin (2 * m + 1) → ℂ) (w : ℂ)
    (c d : ℝ) : Set ℝ :=
  {x | x ∈ Set.Ico c d ∧ laurentEval m a (Circle.exp x : ℂ) = w}

/-- The level-contact set is finite when the corresponding ordinary
polynomial is nonzero. -/
theorem angleLaurentLevelSet_finite (m : ℕ)
    (a : Fin (2 * m + 1) → ℂ) (w : ℂ) (c d : ℝ)
    (hp : shiftedLevelPolynomial m a w ≠ 0)
    (hcd : d - c ≤ 2 * Real.pi) :
    (angleLaurentLevelSet m a w c d).Finite := by
  let u : ℝ → ℂ := fun x ↦ (Circle.exp x : ℂ)
  have hu_inj : Set.InjOn u (angleLaurentLevelSet m a w c d) := by
    intro x hx y hy hxy
    apply Circle.exp_injOn_Ico hcd hx.1 hy.1
    exact Subtype.ext hxy
  apply Set.Finite.of_finite_image (f := u) _ hu_inj
  apply (shiftedLevelPolynomial m a w).roots.finite_toSet.subset
  intro z hz
  obtain ⟨x, hx, rfl⟩ := hz
  change (Circle.exp x : ℂ) ∈ (shiftedLevelPolynomial m a w).roots
  rw [Polynomial.mem_roots hp, Polynomial.IsRoot.def,
    eval_shiftedLevelPolynomial m a w (Circle.exp x : ℂ) (Circle.coe_ne_zero _),
    hx.2, sub_self, mul_zero]

/-- Cardinal form of the root-count theorem: a nonconstant level has at most
twice the frequency degree many contacts in a single period. -/
theorem ncard_angleLaurentLevelSet_le_twice_frequency (m : ℕ)
    (a : Fin (2 * m + 1) → ℂ) (w : ℂ) (c d : ℝ)
    (hp : shiftedLevelPolynomial m a w ≠ 0)
    (hcd : d - c ≤ 2 * Real.pi) :
    (angleLaurentLevelSet m a w c d).ncard ≤ 2 * m := by
  let t := angleLaurentLevelSet m a w c d
  have ht : t.Finite := angleLaurentLevelSet_finite m a w c d hp hcd
  rw [Set.ncard_eq_toFinset_card t ht]
  apply card_angle_laurent_level_le_twice_frequency m a w ht.toFinset c d hp hcd
  · intro x hx
    exact (ht.mem_toFinset.mp hx).1
  · intro x hx
    exact (ht.mem_toFinset.mp hx).2

end Erdos228
