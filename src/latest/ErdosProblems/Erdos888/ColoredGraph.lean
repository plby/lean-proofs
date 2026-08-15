import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Coloured finite bipartite graphs

This file supplies the finite graph estimate used in the proof of Erdős
problem 888.  A graph is represented by a relation between two finite types.
All counting functions take values in `ℝ`; their summands are zero-one
indicators, so they are definitionally the usual edge, two-path, and ordered
rectangle counts (the ordered rectangle count is four times the unlabelled
one).
-/

open scoped BigOperators

namespace Erdos888
namespace ColoredGraph

noncomputable section

attribute [local instance] Classical.propDecidable

universe u v w

/-- A finite bipartite graph, presented as its adjacency relation. -/
abbrev BipartiteGraph (L : Type u) (R : Type v) := L → R → Prop

variable {L : Type u} {R : Type v} [Fintype L] [Fintype R]

/-- The zero-one real indicator of an edge. -/
def edgeIndicator (G : BipartiteGraph L R) (x : L) (y : R) : ℝ :=
  if G x y then 1 else 0

/-- Number of edges, viewed as a real number. -/
def edgeCount (G : BipartiteGraph L R) : ℝ :=
  ∑ y : R, ∑ x : L, edgeIndicator G x y

/-- The finite set of edges of a finite bipartite graph. -/
def edgeFinset (G : BipartiteGraph L R) : Finset (L × R) :=
  Finset.univ.filter fun e ↦ G e.1 e.2

@[simp] lemma mem_edgeFinset (G : BipartiteGraph L R) (x : L) (y : R) :
    (x, y) ∈ edgeFinset G ↔ G x y := by
  simp [edgeFinset]

/-- The real-valued edge sum is the cast of the ordinary edge-finset
cardinality. -/
lemma edgeCount_eq_card_edgeFinset (G : BipartiteGraph L R) :
    edgeCount G = ((edgeFinset G).card : ℝ) := by
  simp only [edgeCount, edgeIndicator, edgeFinset, Finset.card_eq_sum_ones,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Finset.sum_filter,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]

/-- Degree of a right vertex. -/
def rightDegree (G : BipartiteGraph L R) (y : R) : ℝ :=
  ∑ x : L, edgeIndicator G x y

/-- Common right degree of two left vertices. -/
def codegree (G : BipartiteGraph L R) (x x' : L) : ℝ :=
  ∑ y : R, edgeIndicator G x y * edgeIndicator G x' y

/-- Ordered length-two paths with distinct left endpoints. -/
def twoPathCount (G : BipartiteGraph L R) : ℝ :=
  ∑ x : L, ∑ x' : L, if x = x' then 0 else codegree G x x'

/-- Ordered `2 × 2` rectangles.  Each unlabelled rectangle is counted four times. -/
def rectangleCount (G : BipartiteGraph L R) : ℝ :=
  ∑ x : L, ∑ x' : L, if x = x' then 0 else
    ∑ y : R, ∑ y' : R, if y = y' then 0 else
      edgeIndicator G x y * edgeIndicator G x' y *
        edgeIndicator G x y' * edgeIndicator G x' y'

@[simp] lemma edgeIndicator_nonneg (G : BipartiteGraph L R) (x : L) (y : R) :
    0 ≤ edgeIndicator G x y := by
  by_cases h : G x y <;> simp [edgeIndicator, h]

@[simp] lemma edgeIndicator_sq (G : BipartiteGraph L R) (x : L) (y : R) :
    edgeIndicator G x y * edgeIndicator G x y = edgeIndicator G x y := by
  simp [edgeIndicator]

lemma rightDegree_nonneg (G : BipartiteGraph L R) (y : R) :
    0 ≤ rightDegree G y := by
  exact Finset.sum_nonneg fun _ _ ↦ edgeIndicator_nonneg G _ _

lemma codegree_nonneg (G : BipartiteGraph L R) (x x' : L) :
    0 ≤ codegree G x x' := by
  exact Finset.sum_nonneg fun _ _ ↦ mul_nonneg (edgeIndicator_nonneg G _ _)
    (edgeIndicator_nonneg G _ _)

lemma edgeCount_nonneg (G : BipartiteGraph L R) : 0 ≤ edgeCount G := by
  exact Finset.sum_nonneg fun _ _ ↦ rightDegree_nonneg G _

lemma twoPathCount_nonneg (G : BipartiteGraph L R) : 0 ≤ twoPathCount G := by
  apply Finset.sum_nonneg
  intro x hx
  apply Finset.sum_nonneg
  intro x' hx'
  split_ifs
  · exact le_rfl
  · exact codegree_nonneg G x x'

lemma rectangleCount_nonneg (G : BipartiteGraph L R) : 0 ≤ rectangleCount G := by
  apply Finset.sum_nonneg
  intro x hx
  apply Finset.sum_nonneg
  intro x' hx'
  split_ifs
  · exact le_rfl
  · apply Finset.sum_nonneg
    intro y hy
    apply Finset.sum_nonneg
    intro y' hy'
    split_ifs
    · exact le_rfl
    · exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (edgeIndicator_nonneg G _ _) (edgeIndicator_nonneg G _ _))
          (edgeIndicator_nonneg G _ _))
        (edgeIndicator_nonneg G _ _)

lemma edgeCount_eq_sum_rightDegree (G : BipartiteGraph L R) :
    edgeCount G = ∑ y : R, rightDegree G y := by
  rfl

/-! The next two identities are the exact double-counting core of KST. -/

private lemma rightDegree_sq (G : BipartiteGraph L R) (y : R) :
    (rightDegree G y) ^ 2 = rightDegree G y +
      ∑ x : L, ∑ x' : L, if x = x' then 0 else
        edgeIndicator G x y * edgeIndicator G x' y := by
  classical
  simp only [rightDegree, pow_two]
  rw [Finset.sum_mul_sum]
  calc
    (∑ x : L, ∑ x' : L, edgeIndicator G x y * edgeIndicator G x' y) =
        ∑ x : L, ∑ x' : L,
          ((if x = x' then edgeIndicator G x y else 0) +
            (if x = x' then 0 else edgeIndicator G x y * edgeIndicator G x' y)) := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro x' hx'
      by_cases h : x = x'
      · subst x'
        simp [edgeIndicator_sq]
      · simp [h]
    _ = ∑ x : L, (edgeIndicator G x y +
          ∑ x' : L, if x = x' then 0 else
            edgeIndicator G x y * edgeIndicator G x' y) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_add_distrib]
      simp
    _ = _ := by rw [Finset.sum_add_distrib]

lemma sum_rightDegree_sq (G : BipartiteGraph L R) :
    (∑ y : R, (rightDegree G y) ^ 2) = edgeCount G + twoPathCount G := by
  classical
  simp_rw [rightDegree_sq]
  rw [Finset.sum_add_distrib]
  congr 1
  simp only [twoPathCount, codegree]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x' hx'
  by_cases h : x = x' <;> simp [h]

private lemma codegree_sq (G : BipartiteGraph L R) (x x' : L) :
    (codegree G x x') ^ 2 = codegree G x x' +
      ∑ y : R, ∑ y' : R, if y = y' then 0 else
        edgeIndicator G x y * edgeIndicator G x' y *
          edgeIndicator G x y' * edgeIndicator G x' y' := by
  classical
  simp only [codegree, pow_two]
  rw [Finset.sum_mul_sum]
  calc
    (∑ y : R, ∑ y' : R,
        (edgeIndicator G x y * edgeIndicator G x' y) *
          (edgeIndicator G x y' * edgeIndicator G x' y')) =
      ∑ y : R, ∑ y' : R,
        ((if y = y' then edgeIndicator G x y * edgeIndicator G x' y else 0) +
         (if y = y' then 0 else edgeIndicator G x y * edgeIndicator G x' y *
          edgeIndicator G x y' * edgeIndicator G x' y')) := by
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro y' hy'
      by_cases h : y = y'
      · subst y'
        by_cases hxy : G x y <;> by_cases hx'y : G x' y <;>
          simp [edgeIndicator, hxy, hx'y]
      · simp [h]
        ring
    _ = ∑ y : R, (edgeIndicator G x y * edgeIndicator G x' y +
        ∑ y' : R, if y = y' then 0 else edgeIndicator G x y * edgeIndicator G x' y *
          edgeIndicator G x y' * edgeIndicator G x' y') := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.sum_add_distrib]
      simp
    _ = _ := by rw [Finset.sum_add_distrib]

lemma sum_codegree_sq_offDiagonal (G : BipartiteGraph L R) :
    (∑ x : L, ∑ x' : L, if x = x' then 0 else (codegree G x x') ^ 2) =
      twoPathCount G + rectangleCount G := by
  classical
  simp only [twoPathCount, rectangleCount]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x' hx'
  by_cases hxx : x = x'
  · simp [hxx]
  · simp only [hxx, ↓reduceIte, codegree_sq]

/-- First Cauchy--Schwarz step: edges are controlled by right degrees and
ordered two-paths. -/
lemma edgeCount_sq_le (G : BipartiteGraph L R) :
    (edgeCount G) ^ 2 ≤ (Fintype.card R : ℝ) *
      (edgeCount G + twoPathCount G) := by
  rw [edgeCount_eq_sum_rightDegree]
  calc
    (∑ y : R, rightDegree G y) ^ 2 ≤ (Fintype.card R : ℝ) *
        ∑ y : R, (rightDegree G y) ^ 2 := by
      simpa using
        (sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset R))
          (f := rightDegree G))
    _ = _ := by rw [sum_rightDegree_sq, edgeCount_eq_sum_rightDegree]

/-- Second Cauchy--Schwarz step: two-paths are controlled by rectangles. -/
lemma twoPathCount_sq_le (G : BipartiteGraph L R) :
    (twoPathCount G) ^ 2 ≤ (Fintype.card L : ℝ) ^ 2 *
      (twoPathCount G + rectangleCount G) := by
  let f : L × L → ℝ := fun z ↦
    if z.1 = z.2 then 0 else codegree G z.1 z.2
  have hcs := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset (L × L))) (f := f)
  have hsum : (∑ z : L × L, f z) = twoPathCount G := by
    simp only [f, twoPathCount, Fintype.sum_prod_type]
  have hsumsq : (∑ z : L × L, (f z) ^ 2) =
      twoPathCount G + rectangleCount G := by
    simp only [f, Fintype.sum_prod_type]
    simpa only [ite_pow, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      sum_codegree_sq_offDiagonal G
  rw [hsum, hsumsq] at hcs
  simpa [Fintype.card_prod, Nat.cast_mul, pow_two] using hcs

/-! ### The analytic extraction of fourth roots -/

/-- A convenient explicit extraction of the two quadratic estimates in the
Kővári--Sós--Turán argument.  Keeping it separate from the counting makes
the constants and all degenerate terms completely transparent. -/
lemma kst_numeric {E S Q M N : ℝ}
    (hE : 0 ≤ E) (hS : 0 ≤ S) (hQ : 0 ≤ Q) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hES : E ^ 2 ≤ N * (E + S))
    (hSQ : S ^ 2 ≤ M ^ 2 * (S + Q)) :
    E ≤ 2 * N + 2 * M * Real.sqrt N +
      2 * Real.sqrt (M * N) * Real.sqrt (Real.sqrt Q) := by
  have hsN : 0 ≤ Real.sqrt N := Real.sqrt_nonneg N
  have hsMN : 0 ≤ Real.sqrt (M * N) := Real.sqrt_nonneg (M * N)
  have hsQ : 0 ≤ Real.sqrt Q := Real.sqrt_nonneg Q
  have hssQ : 0 ≤ Real.sqrt (Real.sqrt Q) := Real.sqrt_nonneg (Real.sqrt Q)
  have hsN_sq : (Real.sqrt N) ^ 2 = N := Real.sq_sqrt hN
  have hsMN_sq : (Real.sqrt (M * N)) ^ 2 = M * N :=
    Real.sq_sqrt (mul_nonneg hM hN)
  have hsQ_sq : (Real.sqrt Q) ^ 2 = Q := Real.sq_sqrt hQ
  have hssQ_sq : (Real.sqrt (Real.sqrt Q)) ^ 2 = Real.sqrt Q :=
    Real.sq_sqrt hsQ
  by_cases hsmallE : E ≤ 2 * N
  · nlinarith
  have hE_two : 2 * N < E := lt_of_not_ge hsmallE
  have hES' : E ^ 2 ≤ 2 * N * S := by
    nlinarith [mul_nonneg hN hE]
  by_cases hsmallS : S ≤ 2 * M ^ 2
  · have hEroot : E ≤ 2 * M * Real.sqrt N := by
      have hNS := mul_le_mul_of_nonneg_left hsmallS hN
      have hsq : E ^ 2 ≤ (2 * M * Real.sqrt N) ^ 2 := by
        nlinarith [hES', hNS]
      exact (sq_le_sq₀ hE (mul_nonneg (mul_nonneg (by positivity) hM) hsN)).mp hsq
    nlinarith [mul_nonneg hsMN hssQ]
  · have hS_two : 2 * M ^ 2 < S := lt_of_not_ge hsmallS
    have hSQ' : S ^ 2 ≤ 2 * M ^ 2 * Q := by
      nlinarith [mul_nonneg (sq_nonneg M) hS]
    have hSroot : S ≤ 2 * M * Real.sqrt Q := by
      have hsq : S ^ 2 ≤ (2 * M * Real.sqrt Q) ^ 2 := by
        nlinarith [mul_nonneg (sq_nonneg M) hQ]
      exact (sq_le_sq₀ hS (mul_nonneg (mul_nonneg (by positivity) hM) hsQ)).mp hsq
    have hEroot : E ≤ 2 * Real.sqrt (M * N) * Real.sqrt (Real.sqrt Q) := by
      have hNS := mul_le_mul_of_nonneg_left hSroot hN
      have hsq : E ^ 2 ≤
          (2 * Real.sqrt (M * N) * Real.sqrt (Real.sqrt Q)) ^ 2 := by
        nlinarith [hES', hNS]
      exact (sq_le_sq₀ hE
        (mul_nonneg (mul_nonneg (by positivity) hsMN) hssQ)).mp hsq
    nlinarith [mul_nonneg hM hsN]

/-- Rectangle supersaturation / KST with explicit constant `2`, for the
ordered rectangle convention of this file. -/
theorem edgeCount_le (G : BipartiteGraph L R) :
    edgeCount G ≤ 2 * (Fintype.card R : ℝ) +
      2 * (Fintype.card L : ℝ) * Real.sqrt (Fintype.card R : ℝ) +
      2 * Real.sqrt ((Fintype.card L : ℝ) * Fintype.card R) *
        Real.sqrt (Real.sqrt (rectangleCount G)) := by
  apply kst_numeric (hE := edgeCount_nonneg G) (hS := twoPathCount_nonneg G)
    (hQ := rectangleCount_nonneg G) (hM := Nat.cast_nonneg _) (hN := Nat.cast_nonneg _)
    (edgeCount_sq_le G)
  exact twoPathCount_sq_le G

/-! ### Coloured rectangles -/

/-- A specified ordered quadruple is a genuine rectangle in `G`. -/
def ContainsRectangle (G : BipartiteGraph L R) (x x' : L) (y y' : R) : Prop :=
  x ≠ x' ∧ y ≠ y' ∧ G x y ∧ G x' y ∧ G x y' ∧ G x' y'

/-- Indicator of a specified ordered rectangle. -/
def rectangleIndicator (G : BipartiteGraph L R) (x x' : L) (y y' : R) : ℝ :=
  if ContainsRectangle G x x' y y' then 1 else 0

lemma rectangleCount_eq_sum_indicator (G : BipartiteGraph L R) :
    rectangleCount G =
      ∑ x : L, ∑ x' : L, ∑ y : R, ∑ y' : R,
        rectangleIndicator G x x' y y' := by
  classical
  simp only [rectangleCount]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro x' hx'
  by_cases hxx : x = x'
  · simp [hxx, rectangleIndicator, ContainsRectangle]
  simp only [hxx, ↓reduceIte]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro y' hy'
  simp only [rectangleIndicator, ContainsRectangle]
  by_cases hyy : y = y'
  · simp [hyy]
  by_cases h1 : G x y <;> by_cases h2 : G x' y <;>
    by_cases h3 : G x y' <;> by_cases h4 : G x' y' <;>
    simp [hxx, hyy, h1, h2, h3, h4, edgeIndicator]

/-- Distinct colors never contain the same ordered rectangle. -/
def NoRepeatedRectangle {Γ : Type w} [Fintype Γ]
    (G : Γ → BipartiteGraph L R) : Prop :=
  ∀ γ δ, γ ≠ δ → ∀ x x' y y',
    ContainsRectangle (G γ) x x' y y' → ¬ ContainsRectangle (G δ) x x' y y'

variable {Γ : Type w} [Fintype Γ]

private lemma sum_rectangleIndicator_le_one (G : Γ → BipartiteGraph L R)
    (hG : NoRepeatedRectangle G) (x x' : L) (y y' : R) :
    (∑ γ : Γ, rectangleIndicator (G γ) x x' y y') ≤ 1 := by
  classical
  let s : Finset Γ := Finset.univ.filter fun γ ↦ ContainsRectangle (G γ) x x' y y'
  have hs : s.card ≤ 1 := Finset.card_le_one.mpr (by
    intro γ hγ δ hδ
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at hγ hδ
    by_contra hne
    exact (hG γ δ hne x x' y y' hγ) hδ)
  have hsum : (∑ γ : Γ, rectangleIndicator (G γ) x x' y y') = (s.card : ℝ) := by
    simp [rectangleIndicator, s]
  rw [hsum]
  exact_mod_cast hs

/-- Under the no-repetition hypothesis, the total ordered rectangle count is
at most the number of ordered quadruples. -/
theorem sum_rectangleCount_le (G : Γ → BipartiteGraph L R)
    (hG : NoRepeatedRectangle G) :
    (∑ γ : Γ, rectangleCount (G γ)) ≤
      (Fintype.card L : ℝ) ^ 2 * (Fintype.card R : ℝ) ^ 2 := by
  simp_rw [rectangleCount_eq_sum_indicator]
  calc
    (∑ γ : Γ, ∑ x : L, ∑ x' : L, ∑ y : R, ∑ y' : R,
        rectangleIndicator (G γ) x x' y y') =
      ∑ x : L, ∑ x' : L, ∑ y : R, ∑ y' : R, ∑ γ : Γ,
        rectangleIndicator (G γ) x x' y y' := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x' hx'
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.sum_comm]
    _ ≤ ∑ _x : L, ∑ _x' : L, ∑ _y : R, ∑ _y' : R, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro x' hx'
      apply Finset.sum_le_sum
      intro y hy
      apply Finset.sum_le_sum
      intro y' hy'
      exact sum_rectangleIndicator_le_one G hG x x' y y'
    _ = _ := by
      simp [pow_two]
      ring

/-- Finite Hölder at exponent four, in the nested-square-root form used by
the colored KST estimate. -/
lemma sum_sqrt_sqrt_le (f : Γ → ℝ) (hf : ∀ γ, 0 ≤ f γ) :
    (∑ γ : Γ, Real.sqrt (Real.sqrt (f γ))) ≤
      Real.sqrt ((Fintype.card Γ : ℝ) *
        Real.sqrt ((Fintype.card Γ : ℝ) * ∑ γ : Γ, f γ)) := by
  let a : Γ → ℝ := fun γ ↦ Real.sqrt (Real.sqrt (f γ))
  let A : ℝ := ∑ γ : Γ, a γ
  let T : ℝ := Fintype.card Γ
  let Q : ℝ := ∑ γ : Γ, f γ
  let B : ℝ := Real.sqrt (T * Real.sqrt (T * Q))
  have ha : ∀ γ, 0 ≤ a γ := fun γ ↦ Real.sqrt_nonneg _
  have hA : 0 ≤ A := Finset.sum_nonneg fun γ _ ↦ ha γ
  have hT : 0 ≤ T := by simp [T]
  have hQ : 0 ≤ Q := Finset.sum_nonneg fun γ _ ↦ hf γ
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have ha4 : ∀ γ, (a γ) ^ 4 = f γ := by
    intro γ
    have h1 : (Real.sqrt (f γ)) ^ 2 = f γ := Real.sq_sqrt (hf γ)
    have h2 : (Real.sqrt (Real.sqrt (f γ))) ^ 2 = Real.sqrt (f γ) :=
      Real.sq_sqrt (Real.sqrt_nonneg _)
    simp only [a]
    calc
      (Real.sqrt (Real.sqrt (f γ))) ^ 4 =
          ((Real.sqrt (Real.sqrt (f γ))) ^ 2) ^ 2 := by ring
      _ = _ := by rw [h2, h1]
  have hp := pow_sum_le_card_mul_sum_pow
    (s := (Finset.univ : Finset Γ)) (f := a) (fun γ _ ↦ ha γ) 3
  have hp' : A ^ 4 ≤ T ^ 3 * Q := by
    simpa only [A, T, Q, Nat.reduceAdd, Finset.card_univ, ha4] using hp
  have hTQ : 0 ≤ T * Q := mul_nonneg hT hQ
  have hTsqrt : 0 ≤ T * Real.sqrt (T * Q) :=
    mul_nonneg hT (Real.sqrt_nonneg _)
  have hinner : (Real.sqrt (T * Q)) ^ 2 = T * Q := Real.sq_sqrt hTQ
  have houter : B ^ 2 = T * Real.sqrt (T * Q) := by
    simp only [B]
    exact Real.sq_sqrt hTsqrt
  have hB4 : B ^ 4 = T ^ 3 * Q := by
    calc
      B ^ 4 = (B ^ 2) ^ 2 := by ring
      _ = (T * Real.sqrt (T * Q)) ^ 2 := by rw [houter]
      _ = T ^ 3 * Q := by rw [mul_pow, hinner]; ring
  have hfour : A ^ 4 ≤ B ^ 4 := by rwa [hB4]
  have hsq : A ^ 2 ≤ B ^ 2 := by
    apply (sq_le_sq₀ (sq_nonneg A) (sq_nonneg B)).mp
    calc
      (A ^ 2) ^ 2 = A ^ 4 := by ring
      _ ≤ B ^ 4 := hfour
      _ = (B ^ 2) ^ 2 := by ring
  have hAB : A ≤ B := (sq_le_sq₀ hA hB).mp hsq
  simpa only [A, B, T, Q, a] using hAB

/-- Colored KST / rectangle supersaturation.  The first two terms are the
degenerate contribution.  The final nested square root is exactly
`T^(3/4) M N`, written without real powers; thus this is the explicit-constant
version of Lemma 6.2 in the mathematical write-up. -/
theorem sum_edgeCount_le (G : Γ → BipartiteGraph L R)
    (hG : NoRepeatedRectangle G) :
    (∑ γ : Γ, edgeCount (G γ)) ≤
      2 * (Fintype.card Γ : ℝ) * Fintype.card R +
      2 * (Fintype.card Γ : ℝ) * Fintype.card L *
        Real.sqrt (Fintype.card R : ℝ) +
      2 * Real.sqrt ((Fintype.card L : ℝ) * Fintype.card R) *
        Real.sqrt ((Fintype.card Γ : ℝ) *
          Real.sqrt ((Fintype.card Γ : ℝ) *
            (Fintype.card L : ℝ) ^ 2 * (Fintype.card R : ℝ) ^ 2)) := by
  let T : ℝ := Fintype.card Γ
  let M : ℝ := Fintype.card L
  let N : ℝ := Fintype.card R
  let C : ℝ := 2 * Real.sqrt (M * N)
  let D : ℝ := 2 * N + 2 * M * Real.sqrt N
  let Q : Γ → ℝ := fun γ ↦ rectangleCount (G γ)
  have hT : 0 ≤ T := by simp [T]
  have hC : 0 ≤ C := by positivity
  have hsum : (∑ γ : Γ, edgeCount (G γ)) ≤
      T * D + C * ∑ γ : Γ, Real.sqrt (Real.sqrt (Q γ)) := by
    calc
      (∑ γ : Γ, edgeCount (G γ)) ≤
          ∑ γ : Γ, (D + C * Real.sqrt (Real.sqrt (Q γ))) := by
        apply Finset.sum_le_sum
        intro γ hγ
        simpa only [D, C, M, N, Q, add_assoc] using edgeCount_le (G γ)
      _ = T * D + C * ∑ γ : Γ, Real.sqrt (Real.sqrt (Q γ)) := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.mul_sum, Finset.card_univ]
        simp only [T]
  have hholder : (∑ γ : Γ, Real.sqrt (Real.sqrt (Q γ))) ≤
      Real.sqrt (T * Real.sqrt (T * ∑ γ : Γ, Q γ)) := by
    simpa only [T, Q] using
      sum_sqrt_sqrt_le Q (fun γ ↦ rectangleCount_nonneg (G γ))
  have hrect : (∑ γ : Γ, Q γ) ≤ M ^ 2 * N ^ 2 := by
    simpa only [Q, M, N] using sum_rectangleCount_le G hG
  have hinner : T * (∑ γ : Γ, Q γ) ≤ T * (M ^ 2 * N ^ 2) :=
    mul_le_mul_of_nonneg_left hrect hT
  have hsqrtInner : Real.sqrt (T * ∑ γ : Γ, Q γ) ≤
      Real.sqrt (T * (M ^ 2 * N ^ 2)) := Real.sqrt_le_sqrt hinner
  have houter : T * Real.sqrt (T * ∑ γ : Γ, Q γ) ≤
      T * Real.sqrt (T * (M ^ 2 * N ^ 2)) :=
    mul_le_mul_of_nonneg_left hsqrtInner hT
  have hnested : Real.sqrt (T * Real.sqrt (T * ∑ γ : Γ, Q γ)) ≤
      Real.sqrt (T * Real.sqrt (T * (M ^ 2 * N ^ 2))) := Real.sqrt_le_sqrt houter
  calc
    (∑ γ : Γ, edgeCount (G γ)) ≤
        T * D + C * ∑ γ : Γ, Real.sqrt (Real.sqrt (Q γ)) := hsum
    _ ≤ T * D + C * Real.sqrt (T * Real.sqrt (T * ∑ γ : Γ, Q γ)) := by
      gcongr
    _ ≤ T * D + C * Real.sqrt (T * Real.sqrt (T * (M ^ 2 * N ^ 2))) := by
      gcongr
    _ = _ := by
      simp only [T, M, N, C, D]
      ring

end
end ColoredGraph
end Erdos888
