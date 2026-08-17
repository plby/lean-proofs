import Mathlib

/-!
# A finite counting-measure Finner inequality

This file records the elementary `L²` inequality used when one eliminates a
coordinate from the prime-by-prime form of the Montgomery--Vaughan
fundamental lemma.  The measure here is *counting* measure.  Thus a coordinate
which occurs in at least two factors costs no cardinality factor: select two
of the factors, use Cauchy--Schwarz on them, and bound every remaining factor
pointwise by its `L²` norm.

The last theorem packages the same argument with factors not involving the
coordinate pulled outside the sum.  This is the form used in an iterative
finite-product (Finner) argument.
-/

open scoped BigOperators

namespace Erdos220

section PointwiseL2

variable {X : Type*}

/-- A value at one point of a finite set is at most the counting-measure
`L²` norm. -/
lemma le_sqrt_sum_sq {s : Finset X} {f : X → ℝ} {x : X}
    (hx : x ∈ s) (hfx : 0 ≤ f x) :
    f x ≤ Real.sqrt (∑ y ∈ s, f y ^ 2) := by
  have hsum : 0 ≤ ∑ y ∈ s, f y ^ 2 := by positivity
  rw [Real.le_sqrt hfx hsum]
  exact Finset.single_le_sum (fun y hy ↦ sq_nonneg (f y)) hx

end PointwiseL2

section OneCoordinate

variable {X I : Type*} [DecidableEq I]

/-- Generalized Hölder on one finite coordinate, in the special exponent-two
form needed by Montgomery--Vaughan.

For counting measure (rather than probability measure), the hypothesis is
that at least two factors involve the coordinate.  Extra factors only make
the right side larger, since each of them is bounded pointwise by its own
`L²` norm. -/
theorem sum_prod_le_prod_sqrt_sum_sq
    (u : Finset X) (s : Finset I) (f : I → X → ℝ)
    (hs : 2 ≤ s.card) (hf : ∀ i ∈ s, ∀ x ∈ u, 0 ≤ f i x) :
    ∑ x ∈ u, ∏ i ∈ s, f i x ≤
      ∏ i ∈ s, Real.sqrt (∑ x ∈ u, f i x ^ 2) := by
  classical
  obtain ⟨a, ha⟩ := s.card_pos.mp (lt_of_lt_of_le (by omega) hs)
  have hcard_erase : 0 < (s.erase a).card := by
    rw [Finset.card_erase_of_mem ha]
    omega
  obtain ⟨b, hb⟩ := (s.erase a).card_pos.mp hcard_erase
  have hba : b ≠ a := (Finset.mem_erase.mp hb).1
  have hbs : b ∈ s := (Finset.mem_erase.mp hb).2
  let t := (s.erase a).erase b
  let L : I → ℝ := fun i ↦ Real.sqrt (∑ x ∈ u, f i x ^ 2)
  have hL_nonneg (i : I) : 0 ≤ L i := Real.sqrt_nonneg _
  have hpoint (i : I) (hi : i ∈ s) (x : X) (hx : x ∈ u) : f i x ≤ L i := by
    exact le_sqrt_sum_sq hx (hf i hi x hx)
  have ht_subset : t ⊆ s := by
    intro i hi
    exact (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).2
  have hrest (x : X) (hx : x ∈ u) :
      ∏ i ∈ t, f i x ≤ ∏ i ∈ t, L i := by
    exact Finset.prod_le_prod (fun i hi ↦ hf i (ht_subset hi) x hx)
      (fun i hi ↦ hpoint i (ht_subset hi) x hx)
  have hrewrite (g : I → ℝ) :
      ∏ i ∈ s, g i = g a * g b * ∏ i ∈ t, g i := by
    have hbt : b ∉ t := by simp [t]
    have hat : a ∉ t := by simp [t]
    calc
      ∏ i ∈ s, g i = g a * ∏ i ∈ s.erase a, g i := by
        exact (Finset.mul_prod_erase s g ha).symm
      _ = g a * (g b * ∏ i ∈ t, g i) := by
        rw [show ∏ i ∈ s.erase a, g i = g b * ∏ i ∈ t, g i from
          (Finset.mul_prod_erase (s.erase a) g hb).symm]
      _ = g a * g b * ∏ i ∈ t, g i := by ring
  rw [hrewrite L]
  calc
    ∑ x ∈ u, ∏ i ∈ s, f i x =
        ∑ x ∈ u, (f a x * f b x) * ∏ i ∈ t, f i x := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hrewrite (fun i ↦ f i x)]
    _ ≤ ∑ x ∈ u, (f a x * f b x) * ∏ i ∈ t, L i := by
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left (hrest x hx)
        (mul_nonneg (hf a ha x hx) (hf b hbs x hx))
    _ = (∑ x ∈ u, f a x * f b x) * ∏ i ∈ t, L i := by
      rw [Finset.sum_mul]
    _ ≤ (L a * L b) * ∏ i ∈ t, L i := by
      gcongr
      · simpa [L] using
          (Real.sum_mul_le_sqrt_mul_sqrt u (fun x ↦ f a x) (fun x ↦ f b x))
    _ = L a * L b * ∏ i ∈ t, L i := by ring

/-- Coordinate-elimination form of `sum_prod_le_prod_sqrt_sum_sq`.

The factors indexed by `active` vary with the coordinate.  All other factors
are constants and are pulled outside.  This statement is convenient for a
product-coordinate induction: after this step, replace every active factor by
its fiberwise `L²` norm and continue with the remaining coordinates. -/
theorem sum_prod_mul_le_prod_sqrt_sum_sq_mul
    (u : Finset X) (active all : Finset I) (f : I → X → ℝ) (c : I → ℝ)
    (hsub : active ⊆ all) (hactive : 2 ≤ active.card)
    (hf : ∀ i ∈ active, ∀ x ∈ u, 0 ≤ f i x)
    (hc : ∀ i ∈ all \ active, 0 ≤ c i) :
    ∑ x ∈ u, (∏ i ∈ active, f i x) * ∏ i ∈ all \ active, c i ≤
      (∏ i ∈ active, Real.sqrt (∑ x ∈ u, f i x ^ 2)) *
        ∏ i ∈ all \ active, c i := by
  classical
  have hconst : 0 ≤ ∏ i ∈ all \ active, c i :=
    Finset.prod_nonneg hc
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right
    (sum_prod_le_prod_sqrt_sum_sq u active f hactive hf) hconst

end OneCoordinate

section ProductCoordinates

variable {K A : Type*} [Fintype K] [DecidableEq K] [DecidableEq A]

/-- The finite box in which the coordinates in `t` range through their
specified finite sets and all other coordinates are frozen at `base`. -/
def coordinateBox (U : K → Finset A) (base : K → A) (t : Finset K) :
    Finset (K → A) :=
  Fintype.piFinset fun k ↦ if k ∈ t then U k else {base k}

/-- A function on a product depends only on the coordinates in `s`. -/
def DependsOn (f : (K → A) → ℝ) (s : Finset K) : Prop :=
  ∀ x y, (∀ k ∈ s, x k = y k) → f x = f y

/-- The counting-measure `L²` norm of a function on the indicated coordinate
fiber.  Coordinates outside `s` are frozen; `DependsOn f s` makes the value
independent of the chosen base point. -/
noncomputable def coordinateL2 (U : K → Finset A) (base : K → A)
    (s : Finset K) (f : (K → A) → ℝ) : ℝ :=
  Real.sqrt (∑ x ∈ coordinateBox U base s, f x ^ 2)

lemma mem_coordinateBox_iff (U : K → Finset A) (base : K → A)
    (t : Finset K) (x : K → A) :
    x ∈ coordinateBox U base t ↔
      ∀ k, if k ∈ t then x k ∈ U k else x k = base k := by
  rw [coordinateBox, Fintype.mem_piFinset]
  constructor <;> intro h k
  · specialize h k
    by_cases hk : k ∈ t <;> simpa [hk] using h
  · specialize h k
    by_cases hk : k ∈ t <;> simpa [hk] using h

/-- Fubini for a finite product box, splitting off one active coordinate. -/
lemma sum_coordinateBox_eq_sum_erase_sum_update
    (U : K → Finset A) (base : K → A) (t : Finset K) (j : K)
    (hj : j ∈ t) (hbase : base j ∈ U j) (F : (K → A) → ℝ) :
    ∑ x ∈ coordinateBox U base t, F x =
      ∑ y ∈ coordinateBox U base (t.erase j),
        ∑ a ∈ U j, F (Function.update y j a) := by
  classical
  trans ∑ ya ∈ coordinateBox U base (t.erase j) ×ˢ U j,
      F (Function.update ya.1 j ya.2)
  · refine Finset.sum_bij'
      (s := coordinateBox U base t)
      (t := coordinateBox U base (t.erase j) ×ˢ U j)
      (f := F)
      (g := fun ya ↦ F (Function.update ya.1 j ya.2))
      (fun x _ ↦ (Function.update x j (base j), x j))
      (fun ya _ ↦ Function.update ya.1 j ya.2) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_product]
      constructor
      · rw [mem_coordinateBox_iff]
        intro k
        by_cases hkj : k = j
        · subst k
          simp
        · have hmem : k ∈ t.erase j ↔ k ∈ t := by simp [hkj]
          rw [if_congr hmem rfl rfl]
          simpa [Function.update, hkj] using
            (mem_coordinateBox_iff U base t x).mp hx k
      · have := (mem_coordinateBox_iff U base t x).mp hx j
        simpa [hj] using this
    · intro ya hya
      rcases Finset.mem_product.mp hya with ⟨hy, ha⟩
      rw [mem_coordinateBox_iff]
      intro k
      by_cases hkj : k = j
      · subst k
        simp [Function.update, hj, ha]
      · have hmem : k ∈ t.erase j ↔ k ∈ t := by simp [hkj]
        rw [← if_congr hmem rfl rfl]
        simpa [Function.update, hkj] using
          (mem_coordinateBox_iff U base (t.erase j) ya.1).mp hy k
    · intro x hx
      funext k
      by_cases hkj : k = j
      · subst k
        simp [Function.update]
      · simp [Function.update, hkj]
    · intro ya hya
      apply Prod.ext
      · funext k
        by_cases hkj : k = j
        · subst k
          rcases Finset.mem_product.mp hya with ⟨hy, _⟩
          have hfreeze : ya.1 j = base j := by
            simpa using (mem_coordinateBox_iff U base (t.erase j) ya.1).mp hy j
          simpa using hfreeze.symm
        · simp [Function.update, hkj]
      · simp [Function.update]
    · intro x hx
      congr 1
      funext k
      by_cases hkj : k = j
      · subst k
        simp [Function.update]
      · simp [Function.update, hkj]
  · exact Finset.sum_product _ _ _

end ProductCoordinates

end Erdos220
