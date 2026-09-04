import ErdosProblems.Erdos76.LPDuality
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Quadratic optimization on a finite simplex

These lemmas implement weight transfer for the new counting proof of Erdős 76.
No graph classification is used.
-/

open Finset Set
open scoped BigOperators

namespace Erdos76.WeightOptimization

variable {V : Type*} [Fintype V] [DecidableEq V]

def bilinear (A : V → V → ℝ) (p q : V → ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * p i * q j

def quadratic (A : V → V → ℝ) (p : V → ℝ) : ℝ := bilinear A p p

def row (A : V → V → ℝ) (p : V → ℝ) (i : V) : ℝ := ∑ j, A i j * p j

def transfer (p : V → ℝ) (i j : V) (t : ℝ) : V → ℝ :=
  fun k ↦ p k + t * ((if k = i then 1 else 0) - (if k = j then 1 else 0))

lemma bilinear_add_left (A : V → V → ℝ) (p q r : V → ℝ) :
    bilinear A (p + q) r = bilinear A p r + bilinear A q r := by
  simp [bilinear, mul_add, add_mul, sum_add_distrib]

lemma bilinear_add_right (A : V → V → ℝ) (p q r : V → ℝ) :
    bilinear A p (q + r) = bilinear A p q + bilinear A p r := by
  simp [bilinear, mul_add, sum_add_distrib]

lemma bilinear_symmetric (A : V → V → ℝ) (hA : ∀ i j, A i j = A j i)
    (p q : V → ℝ) : bilinear A p q = bilinear A q p := by
  unfold bilinear
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  rw [hA j i]
  ring

lemma bilinear_transfer_right (A : V → V → ℝ) (p q : V → ℝ) (i j : V) (t : ℝ) :
    bilinear A p (transfer q i j t) =
      bilinear A p q + t * (∑ k, A k i * p k) - t * (∑ k, A k j * p k) := by
  simp only [bilinear, transfer, mul_add, mul_sub, sum_add_distrib, sum_sub_distrib]
  simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', Finset.mem_univ, if_true]
  simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro k _
  ring

lemma row_transfer (A : V → V → ℝ) (p : V → ℝ) (i j k : V) (t : ℝ) :
    row A (transfer p i j t) k = row A p k + t * A k i - t * A k j := by
  simp only [row, transfer, mul_add, mul_sub, sum_add_distrib, sum_sub_distrib]
  simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', Finset.mem_univ, if_true]
  ring

lemma quadratic_transfer (A : V → V → ℝ) (hA : ∀ i j, A i j = A j i)
    (p : V → ℝ) (i j : V) (t : ℝ) :
    quadratic A (transfer p i j t) = quadratic A p +
      2 * t * (row A p i - row A p j) +
      t ^ 2 * (A i i + A j j - 2 * A i j) := by
  unfold quadratic
  rw [bilinear_transfer_right, bilinear_symmetric A hA (transfer p i j t) p,
    bilinear_transfer_right]
  simp_rw [hA _ i, hA _ j]
  change bilinear A p p + t * row A p i - t * row A p j +
    t * row A (transfer p i j t) i - t * row A (transfer p i j t) j = _
  rw [row_transfer, row_transfer, hA j i]
  ring

lemma transfer_mem_simplex {p : V → ℝ} (hp : p ∈ stdSimplex ℝ V)
    {i j : V} (hij : i ≠ j) {t : ℝ} (hi : -p i ≤ t) (hj : t ≤ p j) :
    transfer p i j t ∈ stdSimplex ℝ V := by
  constructor
  · intro k
    by_cases hki : k = i
    · subst k
      simp only [transfer, if_true, if_false, hij, sub_zero, mul_one]
      linarith
    · by_cases hkj : k = j
      · subst k
        simp only [transfer, if_true, if_false, Ne.symm hij, zero_sub, mul_neg, mul_one]
        linarith
      · simpa [transfer, hki, hkj] using hp.1 k
  · simp [transfer, sum_add_distrib, mul_sub, sum_sub_distrib, ← mul_sum, hp.2]

lemma continuous_quadratic (A : V → V → ℝ) : Continuous (quadratic A) := by
  unfold quadratic bilinear
  fun_prop

lemma rows_eq_at_max {A : V → V → ℝ} (hA : ∀ i j, A i j = A j i)
    {p : V → ℝ} (hp : p ∈ stdSimplex ℝ V)
    (hmax : ∀ q ∈ stdSimplex ℝ V, quadratic A q ≤ quadratic A p)
    {i j : V} (hi : 0 < p i) (hj : 0 < p j) : row A p i = row A p j := by
  by_cases hij : i = j
  · rw [hij]
  let f : ℝ → ℝ := fun t ↦ quadratic A p +
    2 * t * (row A p i - row A p j) + t ^ 2 * (A i i + A j j - 2 * A i j)
  have hlocal : IsLocalMax f 0 := by
    have hmem : Ioo (-p i) (p j) ∈ nhds (0 : ℝ) :=
      Ioo_mem_nhds (by linarith) hj
    filter_upwards [hmem] with t ht
    have h := hmax (transfer p i j t)
      (transfer_mem_simplex hp hij ht.1.le ht.2.le)
    rw [quadratic_transfer A hA] at h
    simpa [f] using h
  have hderiv : HasDerivAt f (2 * (row A p i - row A p j)) 0 := by
    dsimp [f]
    convert (((hasDerivAt_const (0 : ℝ) (quadratic A p)).add
      (((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const (row A p i - row A p j))).add
      (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (A i i + A j j - 2 * A i j))) using 1 <;>
      first | rfl | norm_num
  have hzero := hlocal.hasDerivAt_eq_zero hderiv
  linarith

lemma row_eq_quadratic_at_max {A : V → V → ℝ} (hA : ∀ i j, A i j = A j i)
    {p : V → ℝ} (hp : p ∈ stdSimplex ℝ V)
    (hmax : ∀ q ∈ stdSimplex ℝ V, quadratic A q ≤ quadratic A p)
    {i : V} (hi : 0 < p i) : row A p i = quadratic A p := by
  calc
    row A p i = ∑ j, p j * row A p i := by rw [← sum_mul, hp.2, one_mul]
    _ = ∑ j, p j * row A p j := by
      apply sum_congr rfl
      intro j _
      by_cases hj : p j = 0
      · simp [hj]
      · rw [rows_eq_at_max hA hp hmax hi (lt_of_le_of_ne (hp.1 j) (Ne.symm hj))]
    _ = quadratic A p := by
      simp only [row, quadratic, bilinear, mul_sum]
      apply sum_congr rfl
      intro j _
      apply sum_congr rfl
      intro k _
      ring

noncomputable def support (p : V → ℝ) : Finset V := by
  classical
  exact univ.filter (fun i ↦ p i ≠ 0)

lemma mem_support {p : V → ℝ} {i : V} : i ∈ support p ↔ p i ≠ 0 := by
  classical
  simp [support]

lemma transfer_support_lt {p : V → ℝ} (hp : p ∈ stdSimplex ℝ V)
    {i j : V} (hij : i ≠ j) (hi : 0 < p i) (hj : 0 < p j) :
    (support (transfer p i j (p j))).card < (support p).card := by
  apply Finset.card_lt_card
  apply ssubset_iff_subset_ne.mpr
  constructor
  · intro k hk
    rw [mem_support] at hk ⊢
    by_cases hki : k = i
    · subst k
      exact hi.ne'
    · by_cases hkj : k = j
      · subst k
        simp [transfer, Ne.symm hij] at hk
      · simpa [transfer, hki, hkj] using hk
  · intro heq
    have hjmem : j ∈ support (transfer p i j (p j)) := heq ▸ mem_support.mpr hj.ne'
    rw [mem_support] at hjmem
    simp [transfer, Ne.symm hij] at hjmem

/-- A quadratic form has a maximizing probability vector for which no pair of
positive coordinates has zero transfer curvature. -/
theorem exists_sparse_maximizer [Nonempty V] (A : V → V → ℝ)
    (hA : ∀ i j, A i j = A j i) :
    ∃ p ∈ stdSimplex ℝ V,
      (∀ q ∈ stdSimplex ℝ V, quadratic A q ≤ quadratic A p) ∧
      (∀ i, 0 < p i → row A p i = quadratic A p) ∧
      ∀ i j, i ≠ j → 0 < p i → 0 < p j → A i i + A j j - 2 * A i j ≠ 0 := by
  classical
  obtain ⟨p₀, hp₀, hm₀⟩ := (isCompact_stdSimplex ℝ V).exists_isMaxOn
    ⟨Pi.single (Classical.arbitrary V) 1, single_mem_stdSimplex ℝ _⟩
    (continuous_quadratic A).continuousOn
  let Maxima := {p : V → ℝ // p ∈ stdSimplex ℝ V ∧
    ∀ q ∈ stdSimplex ℝ V, quadratic A q ≤ quadratic A p}
  have : Nonempty Maxima := ⟨⟨p₀, hp₀, hm₀⟩⟩
  let p : Maxima := Function.argmin (fun q : Maxima ↦ (support q.val).card)
  refine ⟨p.val, p.property.1, p.property.2,
    fun i hi ↦ row_eq_quadratic_at_max hA p.property.1 p.property.2 hi, ?_⟩
  intro i j hij hi hj hzero
  let q := transfer p.val i j (p.val j)
  have hq : q ∈ stdSimplex ℝ V := transfer_mem_simplex p.property.1 hij
    (by linarith) le_rfl
  have heq : quadratic A q = quadratic A p.val := by
    rw [quadratic_transfer A hA, rows_eq_at_max hA p.property.1 p.property.2 hi hj, hzero]
    ring
  let q' : Maxima := ⟨q, hq, fun r hr ↦ heq ▸ p.property.2 r hr⟩
  have hmin : (support p.val).card ≤ (support q).card :=
    Function.argmin_le (fun r : Maxima ↦ (support r.val).card) q'
  exact (not_lt_of_ge hmin) (transfer_support_lt p.property.1 hij hi hj)

end Erdos76.WeightOptimization
