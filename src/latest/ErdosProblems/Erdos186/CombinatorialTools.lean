/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Mathlib

/-!
# Finite combinatorial tools for Erdős Problem 186

This file collects the elementary bookkeeping used when the
Pham--Zakharov argument passes to one of finitely many mass scales and when
successive density restrictions are multiplied.  The statements are kept
independent of the geometric and additive-combinatorial parts of the proof.

There are three groups of results.

* `exists_fiber_mass_ge` and its consequences are weighted pigeonhole
  principles with the exact number of occupied candidate scales.
* `dyadicShell` groups positive natural-valued sizes according to
  `Nat.log 2`; the shell bounds and the mass decomposition have no rounding
  loss.
* `retainedProduct` packages products of retained proportions.  The
  telescoping lemmas retain all powers and constants exactly, and
  `retained_density_cross_mul` gives the division-free density comparison
  used in an iteration.
-/

open scoped BigOperators

namespace Erdos186.CombinatorialTools

/-! ## Weighted finite pigeonhole principles -/

/-- If objects in `s` are assigned to the nonempty finite set `levels`, and
the total mass is at least `levels.card * threshold`, some fiber has mass at
least `threshold`.

The nonnegativity hypothesis is explicit because all applications in the
density argument are to masses.  (The underlying ordered-additive
pigeonhole principle in fact proves the conclusion without it.) -/
theorem exists_fiber_mass_ge
    {alpha beta : Type*} [DecidableEq beta]
    (s : Finset alpha) (levels : Finset beta) (level : alpha → beta)
    (weight : alpha → ℝ) (threshold : ℝ)
    (hlevels : levels.Nonempty)
    (hmaps : ∀ x ∈ s, level x ∈ levels)
    (_hweight : ∀ x ∈ s, 0 ≤ weight x)
    (hmass : (levels.card : ℝ) * threshold ≤ ∑ x ∈ s, weight x) :
    ∃ j ∈ levels, threshold ≤ ∑ x ∈ s.filter (fun x ↦ level x = j), weight x := by
  simpa only [nsmul_eq_mul, Finset.sum_filter] using
    (Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum
      (s := s) (t := levels) (f := level) (w := weight)
      hmaps hlevels (by simpa only [nsmul_eq_mul] using hmass))

/-- Average form of `exists_fiber_mass_ge`: one fiber carries at least the
total mass divided by the number of available levels. -/
theorem exists_fiber_mass_ge_average
    {alpha beta : Type*} [DecidableEq beta]
    (s : Finset alpha) (levels : Finset beta) (level : alpha → beta)
    (weight : alpha → ℝ)
    (hlevels : levels.Nonempty)
    (hmaps : ∀ x ∈ s, level x ∈ levels)
    (hweight : ∀ x ∈ s, 0 ≤ weight x) :
    ∃ j ∈ levels,
      (∑ x ∈ s, weight x) / levels.card ≤
        ∑ x ∈ s.filter (fun x ↦ level x = j), weight x := by
  apply exists_fiber_mass_ge s levels level weight
    ((∑ x ∈ s, weight x) / levels.card) hlevels hmaps hweight
  have hcard : (levels.card : ℝ) ≠ 0 := by
    exact_mod_cast hlevels.card_pos.ne'
  field_simp
  rfl

/-- Division-free average form.  It is often the most convenient exact
mass-scale estimate in later arithmetic. -/
theorem exists_fiber_card_mul_mass_ge
    {alpha beta : Type*} [DecidableEq beta]
    (s : Finset alpha) (levels : Finset beta) (level : alpha → beta)
    (weight : alpha → ℝ)
    (hlevels : levels.Nonempty)
    (hmaps : ∀ x ∈ s, level x ∈ levels)
    (hweight : ∀ x ∈ s, 0 ≤ weight x) :
    ∃ j ∈ levels,
      (∑ x ∈ s, weight x) ≤
        (levels.card : ℝ) *
          ∑ x ∈ s.filter (fun x ↦ level x = j), weight x := by
  obtain ⟨j, hj, hjmass⟩ :=
    exists_fiber_mass_ge_average s levels level weight hlevels hmaps hweight
  refine ⟨j, hj, ?_⟩
  have hcard : (0 : ℝ) < levels.card := by exact_mod_cast hlevels.card_pos
  have h := (div_le_iff₀ hcard).mp hjmass
  simpa [mul_comm] using h

/-- If the total mass is at least `M` and at most `K` scales are available,
some scale has `K * fiberMass ≥ M`.  This is the usual form in which a
logarithmic scale loss is recorded. -/
theorem exists_fiber_mass_of_total
    {alpha beta : Type*} [DecidableEq beta]
    (s : Finset alpha) (levels : Finset beta) (level : alpha → beta)
    (weight : alpha → ℝ) (M K : ℝ)
    (hlevels : levels.Nonempty)
    (hmaps : ∀ x ∈ s, level x ∈ levels)
    (hweight : ∀ x ∈ s, 0 ≤ weight x)
    (hM : M ≤ ∑ x ∈ s, weight x)
    (hK : (levels.card : ℝ) ≤ K) :
    ∃ j ∈ levels,
      M ≤ K * ∑ x ∈ s.filter (fun x ↦ level x = j), weight x := by
  obtain ⟨j, hj, hjmass⟩ :=
    exists_fiber_card_mul_mass_ge s levels level weight hlevels hmaps hweight
  refine ⟨j, hj, hM.trans (hjmass.trans ?_)⟩
  exact mul_le_mul_of_nonneg_right hK
    (Finset.sum_nonneg fun x hx ↦ hweight x (Finset.mem_filter.mp hx).1)

/-! ## Exact dyadic shells -/

/-- The lower binary logarithm, used as the exact dyadic scale of a positive
natural number. -/
def dyadicLevel (n : ℕ) : ℕ := Nat.log 2 n

/-- Elements of `s` whose natural-valued size lies on dyadic level `j`. -/
def dyadicShell {alpha : Type*} [DecidableEq alpha]
    (s : Finset alpha) (size : alpha → ℕ) (j : ℕ) : Finset alpha :=
  s.filter fun x ↦ dyadicLevel (size x) = j

@[simp] theorem mem_dyadicShell
    {alpha : Type*} [DecidableEq alpha] {s : Finset alpha}
    {size : alpha → ℕ} {j : ℕ} {x : alpha} :
    x ∈ dyadicShell s size j ↔ x ∈ s ∧ dyadicLevel (size x) = j := by
  simp [dyadicShell]

/-- Membership in level `j` gives the exact half-open dyadic interval
`[2^j, 2^(j+1))`. -/
theorem dyadicShell_bounds
    {alpha : Type*} [DecidableEq alpha] {s : Finset alpha}
    {size : alpha → ℕ} {j : ℕ} {x : alpha}
    (hx : x ∈ dyadicShell s size j) (hsize : 0 < size x) :
    2 ^ j ≤ size x ∧ size x < 2 ^ (j + 1) := by
  have hlevel : dyadicLevel (size x) = j := (mem_dyadicShell.mp hx).2
  constructor
  · rw [← hlevel]
    exact Nat.pow_log_le_self 2 hsize.ne'
  · rw [← hlevel]
    exact (Nat.log_lt_iff_lt_pow Nat.one_lt_two hsize.ne').mp (Nat.lt_succ_self _)

/-- A positive size below `2^(L+1)` has dyadic level in
`Finset.range (L+1)`. -/
theorem dyadicLevel_mem_range
    {n L : ℕ} (hn : 0 < n) (hupper : n < 2 ^ (L + 1)) :
    dyadicLevel n ∈ Finset.range (L + 1) := by
  exact Finset.mem_range.mpr (Nat.log_lt_of_lt_pow hn.ne' hupper)

/-- Exact decomposition of mass into all dyadic shells through level `L`.
The upper-bound hypothesis says precisely that these shells cover `s`. -/
theorem sum_dyadicShell_eq
    {alpha : Type*} [DecidableEq alpha]
    (s : Finset alpha) (size : alpha → ℕ) (weight : alpha → ℝ) (L : ℕ)
    (hsize : ∀ x ∈ s, 0 < size x)
    (hupper : ∀ x ∈ s, size x < 2 ^ (L + 1)) :
    (∑ j ∈ Finset.range (L + 1), ∑ x ∈ dyadicShell s size j, weight x) =
      ∑ x ∈ s, weight x := by
  have hmaps : ∀ x ∈ s, dyadicLevel (size x) ∈ Finset.range (L + 1) := by
    intro x hx
    exact dyadicLevel_mem_range (hsize x hx) (hupper x hx)
  simpa only [dyadicShell, Finset.sum_filter] using
    (Finset.sum_fiberwise_of_maps_to hmaps weight)

/-- Dyadic mass pigeonhole: one of the `L+1` shells carries at least the
average shell mass, with the exact factor `L+1`. -/
theorem exists_dyadicShell_mass
    {alpha : Type*} [DecidableEq alpha]
    (s : Finset alpha) (size : alpha → ℕ) (weight : alpha → ℝ) (L : ℕ)
    (hsize : ∀ x ∈ s, 0 < size x)
    (hupper : ∀ x ∈ s, size x < 2 ^ (L + 1))
    (hweight : ∀ x ∈ s, 0 ≤ weight x) :
    ∃ j < L + 1,
      (∑ x ∈ s, weight x) ≤
        (L + 1 : ℝ) * ∑ x ∈ dyadicShell s size j, weight x := by
  have hlevels : (Finset.range (L + 1)).Nonempty := by simp
  have hmaps : ∀ x ∈ s, dyadicLevel (size x) ∈ Finset.range (L + 1) := by
    intro x hx
    exact dyadicLevel_mem_range (hsize x hx) (hupper x hx)
  obtain ⟨j, hj, hjmass⟩ := exists_fiber_card_mul_mass_ge s
    (Finset.range (L + 1)) (fun x ↦ dyadicLevel (size x)) weight
    hlevels hmaps hweight
  refine ⟨j, Finset.mem_range.mp hj, ?_⟩
  simpa [dyadicShell] using hjmass

/-- Cardinality specialization of the dyadic mass pigeonhole. -/
theorem exists_dyadicShell_card
    {alpha : Type*} [DecidableEq alpha]
    (s : Finset alpha) (size : alpha → ℕ) (L : ℕ)
    (hsize : ∀ x ∈ s, 0 < size x)
    (hupper : ∀ x ∈ s, size x < 2 ^ (L + 1)) :
    ∃ j < L + 1, s.card ≤ (L + 1) * (dyadicShell s size j).card := by
  obtain ⟨j, hj, hjcard⟩ :=
    exists_dyadicShell_mass s size (fun _ ↦ (1 : ℝ)) L hsize hupper (by simp)
  refine ⟨j, hj, ?_⟩
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hjcard
  exact_mod_cast hjcard

/-! ## Retained proportions and telescoping products -/

/-- Product of the first `n` retained proportions. -/
def retainedProduct (ratio : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n, ratio i

@[simp] theorem retainedProduct_zero (ratio : ℕ → ℝ) :
    retainedProduct ratio 0 = 1 := by
  simp [retainedProduct]

theorem retainedProduct_succ (ratio : ℕ → ℝ) (n : ℕ) :
    retainedProduct ratio (n + 1) = retainedProduct ratio n * ratio n := by
  simp [retainedProduct, Finset.prod_range_succ]

/-- A product of nonnegative retained proportions is nonnegative. -/
theorem retainedProduct_nonneg
    (ratio : ℕ → ℝ) (n : ℕ) (hratio : ∀ i < n, 0 ≤ ratio i) :
    0 ≤ retainedProduct ratio n := by
  exact Finset.prod_nonneg fun i hi ↦ hratio i (Finset.mem_range.mp hi)

/-- If every retained proportion is at most one, so is their product. -/
theorem retainedProduct_le_one
    (ratio : ℕ → ℝ) (n : ℕ)
    (hratio₀ : ∀ i < n, 0 ≤ ratio i) (hratio₁ : ∀ i < n, ratio i ≤ 1) :
    retainedProduct ratio n ≤ 1 := by
  simpa [retainedProduct] using Finset.prod_le_one
    (fun i hi ↦ hratio₀ i (Finset.mem_range.mp hi))
    (fun i hi ↦ hratio₁ i (Finset.mem_range.mp hi))

/-- Exact lower product bound for accumulated relative losses. -/
theorem one_sub_sum_le_retainedProduct
    (loss : ℕ → ℝ) (n : ℕ)
    (hloss₀ : ∀ i < n, 0 ≤ loss i) (hloss₁ : ∀ i < n, loss i ≤ 1) :
    1 - ∑ i ∈ Finset.range n, loss i ≤
      retainedProduct (fun i ↦ 1 - loss i) n := by
  induction n with
  | zero => simp [retainedProduct]
  | succ n ih =>
      have hn₀ := hloss₀ n (Nat.lt_succ_self n)
      have hn₁ := hloss₁ n (Nat.lt_succ_self n)
      have hsum₀ : 0 ≤ ∑ i ∈ Finset.range n, loss i :=
        Finset.sum_nonneg fun i hi ↦
          hloss₀ i ((Finset.mem_range.mp hi).trans (Nat.lt_succ_self n))
      have hih := ih
        (fun i hi ↦ hloss₀ i (hi.trans (Nat.lt_succ_self n)))
        (fun i hi ↦ hloss₁ i (hi.trans (Nat.lt_succ_self n)))
      rw [Finset.sum_range_succ, retainedProduct_succ]
      calc
        1 - ((∑ i ∈ Finset.range n, loss i) + loss n) ≤
            (1 - ∑ i ∈ Finset.range n, loss i) * (1 - loss n) := by
              nlinarith
        _ ≤ retainedProduct (fun i ↦ 1 - loss i) n * (1 - loss n) :=
          mul_le_mul_of_nonneg_right hih (sub_nonneg.mpr hn₁)

/-- If the accumulated losses are at most `eta`, at least `1-eta` of the
multiplicative density is retained. -/
theorem one_sub_budget_le_retainedProduct
    (loss : ℕ → ℝ) (n : ℕ) (eta : ℝ)
    (hloss₀ : ∀ i < n, 0 ≤ loss i) (hloss₁ : ∀ i < n, loss i ≤ 1)
    (hbudget : ∑ i ∈ Finset.range n, loss i ≤ eta) :
    1 - eta ≤ retainedProduct (fun i ↦ 1 - loss i) n := by
  exact (sub_le_sub_left hbudget 1).trans
    (one_sub_sum_le_retainedProduct loss n hloss₀ hloss₁)

/-- Per-step lower retention inequalities telescope without any loss. -/
theorem retainedProduct_mul_initial_le_final
    (ratio mass : ℕ → ℝ) (n : ℕ)
    (hratio : ∀ i < n, 0 ≤ ratio i)
    (hstep : ∀ i < n, ratio i * mass i ≤ mass (i + 1)) :
    retainedProduct ratio n * mass 0 ≤ mass n := by
  induction n with
  | zero => simp [retainedProduct]
  | succ n ih =>
      have hprefix := ih
        (fun i hi ↦ hratio i (hi.trans (Nat.lt_succ_self n)))
        (fun i hi ↦ hstep i (hi.trans (Nat.lt_succ_self n)))
      rw [retainedProduct_succ]
      calc
        (retainedProduct ratio n * ratio n) * mass 0 =
            ratio n * (retainedProduct ratio n * mass 0) := by ring
        _ ≤ ratio n * mass n :=
          mul_le_mul_of_nonneg_left hprefix (hratio n (Nat.lt_succ_self n))
        _ ≤ mass (n + 1) := hstep n (Nat.lt_succ_self n)

/-- Per-step upper shrinkage by the `K`-th power of each retained
proportion telescopes to the `K`-th power of their product. -/
theorem final_le_retainedProduct_pow_mul_initial
    (ratio box : ℕ → ℝ) (K n : ℕ)
    (hratio : ∀ i < n, 0 ≤ ratio i)
    (hstep : ∀ i < n, box (i + 1) ≤ ratio i ^ K * box i) :
    box n ≤ retainedProduct ratio n ^ K * box 0 := by
  induction n with
  | zero => simp [retainedProduct]
  | succ n ih =>
      have hprefix := ih
        (fun i hi ↦ hratio i (hi.trans (Nat.lt_succ_self n)))
        (fun i hi ↦ hstep i (hi.trans (Nat.lt_succ_self n)))
      have hpow : 0 ≤ ratio n ^ K := pow_nonneg (hratio n (Nat.lt_succ_self n)) _
      calc
        box (n + 1) ≤ ratio n ^ K * box n := hstep n (Nat.lt_succ_self n)
        _ ≤ ratio n ^ K * (retainedProduct ratio n ^ K * box 0) :=
          mul_le_mul_of_nonneg_left hprefix hpow
        _ = retainedProduct ratio (n + 1) ^ K * box 0 := by
          rw [retainedProduct_succ, mul_pow]
          ring

/-- Division-free comparison of the `K`-th-power density.  If points retain
a factor `ratio i` while the ambient box shrinks by `ratio i ^ K`, then
`points^K / box` cannot decrease. -/
theorem retained_density_cross_mul
    (ratio points box : ℕ → ℝ) (K n : ℕ)
    (hratio : ∀ i < n, 0 ≤ ratio i)
    (hpoints₀ : 0 ≤ points 0) (hbox₀ : 0 ≤ box 0)
    (hpoints : ∀ i < n, ratio i * points i ≤ points (i + 1))
    (hbox : ∀ i < n, box (i + 1) ≤ ratio i ^ K * box i) :
    box n * points 0 ^ K ≤ box 0 * points n ^ K := by
  have hprod₀ : 0 ≤ retainedProduct ratio n :=
    retainedProduct_nonneg ratio n hratio
  have hp := retainedProduct_mul_initial_le_final ratio points n hratio hpoints
  have hb := final_le_retainedProduct_pow_mul_initial ratio box K n hratio hbox
  calc
    box n * points 0 ^ K ≤
        (retainedProduct ratio n ^ K * box 0) * points 0 ^ K :=
      mul_le_mul_of_nonneg_right hb (pow_nonneg hpoints₀ _)
    _ = box 0 * (retainedProduct ratio n * points 0) ^ K := by
      rw [mul_pow]
      ring
    _ ≤ box 0 * points n ^ K := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (mul_nonneg hprod₀ hpoints₀) hp K) hbox₀

end Erdos186.CombinatorialTools
