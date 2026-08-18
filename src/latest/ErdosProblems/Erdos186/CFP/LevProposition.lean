/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Elementary

/-!
# The numerical core of Lev's Proposition 1

This file isolates the finite arithmetic argument in Proposition 1(ii) of
V. F. Lev, *Consecutive integers in high-multiplicity sumsets* (2010).
The set-theoretic input to that proposition gives the lower bound

`1 + ∑ j < k, min (ell j) ((j + 1) * (n - 2) + 1)`

for the cardinality of an iterated sumset, where `ell j` are the diameters of
the summands in nondecreasing order.  The results below prove that this lower
bound is at least half of

`(∑ j < k, ell j) + k * (n - 1) + 2`.

The proof pairs the term at index `i` with the term at the reflected index
`k - 1 - i`.  It is deliberately independent of the additive-combinatorial
growth theorem, so that theorem can be connected through the final packaging
lemma `of_growth_bound`.
-/

namespace Erdos186.CFP.LevProposition

open scoped BigOperators

/-! ## The reflected two-term estimate -/

/-- The signed two-term inequality behind Lev's red/blue block argument.

Here `a = n - 2`, `x` and `y` are two diameters, and the one-based indices
are `i + 1` and `j + 1`.  The relation `i + j + 1 = k` says that the indices
are reflected in a list of length `k`. -/
private theorem pair_min_ge (a k i j x y : ℤ)
    (ha : 1 ≤ a) (hi : 0 ≤ i) (hij : i ≤ j) (hk : i + j + 1 = k)
    (hx : a + 1 ≤ x) (hxy : x ≤ y) (hy : y ≤ k * a + 1) :
    2 * (a + 1) ≤
      (2 * min x ((i + 1) * a + 1) - x) +
        (2 * min y ((j + 1) * a + 1) - y) := by
  subst k
  have hai : 0 ≤ i * a := mul_nonneg hi (by omega)
  have haji : 0 ≤ (j - i) * a := mul_nonneg (sub_nonneg.mpr hij) (by omega)
  rcases le_total x ((i + 1) * a + 1) with hxi | hix
  · rw [min_eq_left hxi]
    rcases le_total y ((j + 1) * a + 1) with hyj | hjy
    · rw [min_eq_left hyj]
      omega
    · rw [min_eq_right hjy]
      nlinarith
  · rw [min_eq_right hix]
    rcases le_total y ((j + 1) * a + 1) with hyj | hjy
    · rw [min_eq_left hyj]
      nlinarith
    · rw [min_eq_right hjy]
      nlinarith

/-! ## Summing the reflected estimates -/

/-- The signed contribution of the summand of diameter `x` at zero-based
index `i`, with `a = n - 2`. -/
private def signedTerm (a i x : ℕ) : ℤ :=
  2 * (min x ((i + 1) * a + 1) : ℕ) - x

/-- Each signed contribution and its reflection contribute at least
`2 * (a + 1)`. -/
private theorem signedTerm_add_reflect_ge {k q a : ℕ} (ell : ℕ → ℕ)
    (ha : 1 ≤ a)
    (hmono : ∀ {i j}, i < k → j < k → i ≤ j → ell i ≤ ell j)
    (hlower : ∀ i < k, a + 1 ≤ ell i)
    (hupper : ∀ i < k, ell i ≤ q)
    (hk : q - 1 ≤ k * a) {i : ℕ} (hi : i < k) :
    ((2 * (a + 1) : ℕ) : ℤ) ≤
      signedTerm a i (ell i) + signedTerm a (k - 1 - i) (ell (k - 1 - i)) := by
  let j := k - 1 - i
  have hj : j < k := by
    dsimp [j]
    omega
  have hijsum : i + j + 1 = k := by
    dsimp [j]
    omega
  have hqpos : 1 ≤ q := by
    have := hlower i hi
    have := hupper i hi
    omega
  have hq : q ≤ k * a + 1 := by omega
  by_cases hij : i ≤ j
  · have hpair := pair_min_ge (a : ℤ) (k : ℤ) (i : ℤ) (j : ℤ)
        (ell i : ℤ) (ell j : ℤ)
        (by exact_mod_cast ha) (by omega) (by exact_mod_cast hij)
        (by exact_mod_cast hijsum) (by exact_mod_cast hlower i hi)
        (by exact_mod_cast hmono hi hj hij)
        (by exact_mod_cast (le_trans (hupper j hj) hq))
    simpa [signedTerm, j] using hpair
  · have hji : j ≤ i := by omega
    have hpair := pair_min_ge (a : ℤ) (k : ℤ) (j : ℤ) (i : ℤ)
        (ell j : ℤ) (ell i : ℤ)
        (by exact_mod_cast ha) (by omega) (by exact_mod_cast hji)
        (by rw [add_comm i j] at hijsum; exact_mod_cast hijsum)
        (by exact_mod_cast hlower j hj) (by exact_mod_cast hmono hj hi hji)
        (by exact_mod_cast (le_trans (hupper i hi) hq))
    simpa [signedTerm, j, add_comm] using hpair

/-- Abstract arithmetic form of Proposition 1(ii), with `a` standing for
`n - 2`.  The hypotheses say that the nondecreasing diameters lie between
`a + 1` and `q`, and that the last one-based threshold `k * a` reaches
`q - 1`. -/
theorem sum_min_growth_bound_aux {k q a : ℕ} (ell : ℕ → ℕ)
    (ha : 1 ≤ a)
    (hmono : ∀ {i j}, i < k → j < k → i ≤ j → ell i ≤ ell j)
    (hlower : ∀ i < k, a + 1 ≤ ell i)
    (hupper : ∀ i < k, ell i ≤ q)
    (hk : q - 1 ≤ k * a) :
    (∑ i ∈ Finset.range k, ell i) + k * (a + 1) ≤
      2 * ∑ i ∈ Finset.range k, min (ell i) ((i + 1) * a + 1) := by
  have hsum :
      ∑ i ∈ Finset.range k, ((2 * (a + 1) : ℕ) : ℤ) ≤
        ∑ i ∈ Finset.range k,
          (signedTerm a i (ell i) + signedTerm a (k - 1 - i) (ell (k - 1 - i))) := by
    exact Finset.sum_le_sum fun i hi ↦
      signedTerm_add_reflect_ge ell ha hmono hlower hupper hk (Finset.mem_range.mp hi)
  rw [Finset.sum_add_distrib] at hsum
  rw [Finset.sum_range_reflect (fun i ↦ signedTerm a i (ell i)) k] at hsum
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  simp_rw [signedTerm] at hsum
  have hcast :
      (((∑ i ∈ Finset.range k, ell i) + k * (a + 1) : ℕ) : ℤ) ≤
        ((2 * ∑ i ∈ Finset.range k,
          min (ell i) ((i + 1) * a + 1) : ℕ) : ℤ) := by
    push_cast
    rw [Finset.sum_sub_distrib] at hsum
    push_cast at hsum
    rw [← Finset.mul_sum] at hsum
    nlinarith
  exact_mod_cast hcast

/-- Proposition 1(ii)'s numerical inequality in the notation used for
sumsets: `ell i` is the diameter of the `(i + 1)`-st summand. -/
theorem sum_min_growth_bound {k q n : ℕ} (ell : ℕ → ℕ)
    (hn : 3 ≤ n)
    (hmono : ∀ {i j}, i < k → j < k → i ≤ j → ell i ≤ ell j)
    (hlower : ∀ i < k, n - 1 ≤ ell i)
    (hupper : ∀ i < k, ell i ≤ q)
    (hk : q - 1 ≤ k * (n - 2)) :
    (∑ i ∈ Finset.range k, ell i) + k * (n - 1) ≤
      2 * ∑ i ∈ Finset.range k,
        min (ell i) ((i + 1) * (n - 2) + 1) := by
  have hstep : n - 2 + 1 = n - 1 := by omega
  simpa only [hstep] using
    (sum_min_growth_bound_aux (a := n - 2) ell (by omega) hmono
      (fun i hi ↦ by simpa only [hstep] using hlower i hi) hupper hk)

/-- Packaging form used after an application of Lev's additive growth
theorem.  `total` is the cardinality of the iterated sumset and `diameter`
is its diameter.  The two input inequalities are precisely the only facts
about sets needed by the numerical argument. -/
theorem of_growth_bound {k q n total diameter : ℕ} (ell : ℕ → ℕ)
    (hn : 3 ≤ n)
    (hmono : ∀ {i j}, i < k → j < k → i ≤ j → ell i ≤ ell j)
    (hlower : ∀ i < k, n - 1 ≤ ell i)
    (hupper : ∀ i < k, ell i ≤ q)
    (hk : q - 1 ≤ k * (n - 2))
    (hdiameter : diameter ≤ ∑ i ∈ Finset.range k, ell i)
    (hgrowth :
      1 + ∑ i ∈ Finset.range k,
        min (ell i) ((i + 1) * (n - 2) + 1) ≤ total) :
    diameter + k * (n - 1) + 2 ≤ 2 * total := by
  have hnum := sum_min_growth_bound ell hn hmono hlower hupper hk
  omega

/-! ## Alternating balance -/

/-- If a nondecreasing list of `2 * k` natural-number weights is split into
its even and odd positions, then the odd-position sum exceeds the
even-position sum by at most a common upper bound for the weights. -/
theorem odd_sum_le_even_sum_add {k q : ℕ} (w : ℕ → ℕ)
    (hmono : ∀ {i j}, i < 2 * k → j < 2 * k → i ≤ j → w i ≤ w j)
    (hupper : ∀ i < 2 * k, w i ≤ q) :
    (∑ i ∈ Finset.range k, w (2 * i + 1)) ≤
      (∑ i ∈ Finset.range k, w (2 * i)) + q := by
  cases k with
  | zero => simp
  | succ m =>
      have hpair :
          (∑ i ∈ Finset.range m, w (2 * i + 1)) ≤
            ∑ i ∈ Finset.range m, w (2 * (i + 1)) := by
        exact Finset.sum_le_sum fun i hi ↦
          hmono (by have := Finset.mem_range.mp hi; omega)
            (by have := Finset.mem_range.mp hi; omega) (by omega)
      have hlast : w (2 * m + 1) ≤ q := hupper _ (by omega)
      have heven :
          (∑ i ∈ Finset.range (m + 1), w (2 * i)) =
            w 0 + ∑ i ∈ Finset.range m, w (2 * (i + 1)) := by
        rw [show m + 1 = 1 + m by omega, Finset.sum_range_add]
        simp only [Finset.sum_range_one, mul_zero, Nat.add_comm 1]
      calc
        (∑ i ∈ Finset.range (m + 1), w (2 * i + 1)) =
            (∑ i ∈ Finset.range m, w (2 * i + 1)) + w (2 * m + 1) := by
              rw [Finset.sum_range_succ]
        _ ≤ (∑ i ∈ Finset.range m, w (2 * (i + 1))) + q :=
          Nat.add_le_add hpair hlast
        _ ≤ (∑ i ∈ Finset.range (m + 1), w (2 * i)) + q := by
          rw [heven]
          omega

end Erdos186.CFP.LevProposition
