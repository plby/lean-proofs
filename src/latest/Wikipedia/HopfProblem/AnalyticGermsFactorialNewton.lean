import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Data.Multiset.Fintype
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Complex.Basic

/-!
# Analytic polynomial coefficients reconstructed from power sums

Newton's identities reconstruct elementary symmetric functions from power
sums using only finite sums, products, and division by positive integers.
Consequently, analytic power sums give analytic coefficients without choosing
or ordering individual roots.  This is the algebraic part of the convergent
Weierstrass construction.
-/

noncomputable section

open Finset

namespace Wikipedia.HopfProblem.AnalyticGermsFactorial.Newton

/-- Elementary symmetric coefficients reconstructed from a sequence of power
sums.  The zeroth power sum does not enter this recursion. -/
def elementary (s : ℕ → ℂ) : ℕ → ℂ
  | 0 => 1
  | n + 1 => (n + 1 : ℂ)⁻¹ * (-1) ^ (n + 2) *
      ∑ i : Fin (n + 1), (-1) ^ (i : ℕ) * elementary s i * s (n + 1 - i)
termination_by n => n

@[simp] theorem elementary_zero (s : ℕ → ℂ) : elementary s 0 = 1 := by
  rw [elementary]

theorem elementary_succ (s : ℕ → ℂ) (n : ℕ) :
    elementary s (n + 1) = (n + 1 : ℂ)⁻¹ * (-1) ^ (n + 2) *
      ∑ i : Fin (n + 1), (-1) ^ (i : ℕ) * elementary s i * s (n + 1 - i) := by
  rw [elementary]

private theorem sum_antidiagonal_lt (n : ℕ) (f : ℕ → ℕ → ℂ) :
    (∑ a ∈ antidiagonal n with a.1 < n, f a.1 a.2) =
      ∑ i : Fin n, f i (n - i) := by
  change (∑ a ∈ antidiagonal n with a.1 < n, f a.1 a.2) =
    ∑ i : Fin n, (fun j : ℕ => f j (n - j)) i
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => f j (n - j))]
  refine Finset.sum_nbij' Prod.fst (fun i => (i, n - i)) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    exact mem_range.mpr (mem_filter.mp ha).2
  · intro i hi
    exact mem_filter.mpr ⟨mem_antidiagonal.mpr (Nat.add_sub_of_le
      (Nat.le_of_lt (mem_range.mp hi))), mem_range.mp hi⟩
  · intro a ha
    have ha' := mem_antidiagonal.mp (mem_filter.mp ha).1
    exact Prod.ext rfl (by omega)
  · intro i hi
    rfl
  · intro a ha
    have ha' := mem_antidiagonal.mp (mem_filter.mp ha).1
    congr 1
    omega

/-- Newton's identities evaluated at an arbitrary finite multiset, with its
actual multiplicities. -/
theorem multiset_newton (m : Multiset ℂ) (n : ℕ) :
    (n : ℂ) * m.esymm n = (-1) ^ (n + 1) *
      ∑ i : Fin n, (-1) ^ (i : ℕ) * m.esymm i *
        (m.map (fun z => z ^ (n - i))).sum := by
  classical
  have h := congrArg (MvPolynomial.aeval (fun x : m => (x : ℂ)))
    (MvPolynomial.mul_esymm_eq_sum m ℂ n)
  simp only [map_mul, map_natCast, map_pow, map_neg, map_one,
    map_sum, MvPolynomial.aeval_esymm_eq_multiset_esymm,
    Multiset.map_univ_coe, MvPolynomial.psum, MvPolynomial.aeval_X] at h
  change (n : ℂ) * m.esymm n = (-1) ^ (n + 1) *
    ∑ a ∈ antidiagonal n with a.1 < n,
      (-1) ^ a.1 * m.esymm a.1 * ∑ x : m, (x : ℂ) ^ a.2 at h
  rw [sum_antidiagonal_lt n (fun i j =>
    (-1) ^ i * m.esymm i * ∑ x : m, (x : ℂ) ^ j)] at h
  convert h using 2
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  rw [Finset.sum_eq_multiset_sum, ← Multiset.map_univ m (fun z => z ^ (n - i))]

/-- The recursively reconstructed coefficients are exactly the elementary
symmetric functions of any multiset with the prescribed power sums. -/
theorem elementary_eq_esymm (m : Multiset ℂ) (n : ℕ) :
    elementary (fun k => (m.map (fun z => z ^ k)).sum) n = m.esymm n := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp [Multiset.esymm]
      | succ n =>
          rw [elementary_succ]
          have h := multiset_newton m (n + 1)
          have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
          simp only [Nat.cast_add, Nat.cast_one] at h
          rw [show (∑ i : Fin (n + 1), (-1) ^ (i : ℕ) *
              elementary (fun k => (m.map (fun z => z ^ k)).sum) i *
                (m.map (fun z => z ^ (n + 1 - i))).sum) =
              ∑ i : Fin (n + 1), (-1) ^ (i : ℕ) * m.esymm i *
                (m.map (fun z => z ^ (n + 1 - i))).sum by
            apply Finset.sum_congr rfl
            intro i hi
            rw [ih i i.isLt]]
          calc
            _ = (n + 1 : ℂ)⁻¹ * ((n + 1 : ℂ) * m.esymm (n + 1)) := by
              simpa only [mul_assoc, Nat.add_assoc] using
                congrArg ((n + 1 : ℂ)⁻¹ * ·) h.symm
            _ = m.esymm (n + 1) := by rw [inv_mul_cancel_left₀ hn]

section Analytic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Reconstruction from analytic moments is analytic; this does not require
individual roots to depend continuously on the parameter. -/
theorem elementary_analyticAt (s : ℕ → E → ℂ) {a : E}
    (hs : ∀ k, AnalyticAt ℂ (s k) a) (n : ℕ) :
    AnalyticAt ℂ (fun z => elementary (fun k => s k z) n) a := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simpa only [elementary_zero] using (analyticAt_const (v := (1 : ℂ)))
      | succ n =>
          simp only [elementary_succ]
          apply AnalyticAt.mul analyticAt_const
          apply Finset.analyticAt_fun_sum
          intro i hi
          exact (analyticAt_const.mul (ih i i.isLt)).mul (hs _)

/-- The same statement on any parameter set. -/
theorem elementary_analyticOnNhd (s : ℕ → E → ℂ) {U : Set E}
    (hs : ∀ k, AnalyticOnNhd ℂ (s k) U) (n : ℕ) :
    AnalyticOnNhd ℂ (fun z => elementary (fun k => s k z) n) U :=
  fun a ha => elementary_analyticAt s (fun k => hs k a ha) n

end Analytic

/-- The monic degree-`d` polynomial with coefficients reconstructed from
power sums. -/
def polynomial (s : ℕ → ℂ) (d : ℕ) : Polynomial ℂ :=
  ∑ j ∈ range (d + 1), (-1) ^ j *
    (Polynomial.C (elementary s j) * Polynomial.X ^ (d - j))

/-- For the power sums of actual roots, reconstruction is the genuine product
of the corresponding linear factors. -/
theorem polynomial_eq_multiset_prod (m : Multiset ℂ) :
    polynomial (fun k => (m.map (fun z => z ^ k)).sum) m.card =
      (m.map (fun z => Polynomial.X - Polynomial.C z)).prod := by
  rw [Multiset.prod_X_sub_X_eq_sum_esymm]
  simp only [polynomial, elementary_eq_esymm]

end Wikipedia.HopfProblem.AnalyticGermsFactorial.Newton
