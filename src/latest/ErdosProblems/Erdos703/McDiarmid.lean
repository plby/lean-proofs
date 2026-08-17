/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# A finite weighted McDiarmid inequality

This file proves bounded-differences concentration for an arbitrary finite product
distribution.  The coordinates may have different probability weights (and hence the
specialization to `Bool` includes independent, non-identically distributed biased coins).

The proof is finite and elementary apart from Hoeffding's lemma, for which we use the
proved theorem in Mathlib.  All probabilities below are represented explicitly as finite
weighted sums, so consumers do not have to set up measure-theoretic independence.
-/

namespace Erdos703McDiarmid

open scoped BigOperators ENNReal NNReal
open Finset Function MeasureTheory ProbabilityTheory Real

attribute [local instance] Classical.propDecidable

noncomputable section

variable {α : Type*} [Fintype α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The mass of a point in a finite product distribution. -/
def productMass {n : ℕ} (w : Fin n → α → ℝ) (x : Fin n → α) : ℝ :=
  ∏ i, w i (x i)

/-- The (normalized, when the coordinate weights are normalized) weighted expectation. -/
def weightedMean {n : ℕ} (w : Fin n → α → ℝ) (f : (Fin n → α) → ℝ) : ℝ :=
  ∑ x, productMass w x * f x

/-- A finite probability measure associated to normalized real weights. -/
def finiteWeightMeasure (w : α → ℝ) : Measure α :=
  Measure.sum fun a ↦ ENNReal.ofReal (w a) • Measure.dirac a

lemma finiteWeightMeasure_isProbability (w : α → ℝ)
    (hw0 : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1) :
    IsProbabilityMeasure (finiteWeightMeasure w) := by
  unfold finiteWeightMeasure
  apply HasSum.isProbabilityMeasure_sum_dirac hw0
  simpa [hw1] using hasSum_fintype w

lemma integral_finiteWeightMeasure (w : α → ℝ) (hw0 : ∀ a, 0 ≤ w a)
    (g : α → ℝ) :
    ∫ a, g a ∂finiteWeightMeasure w = ∑ a, w a * g a := by
  rw [finiteWeightMeasure, integral_sum_dirac (by simp)]
  simp only [ENNReal.toReal_ofReal (hw0 _), smul_eq_mul, tsum_fintype]

/-- Hoeffding's lemma for a finite normalized weighted sum. -/
lemma finite_weighted_hoeffding (w : α → ℝ) (g : α → ℝ) (lo hi lam : ℝ)
    (hw0 : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (hg : ∀ a, g a ∈ Set.Icc lo hi) :
    ∑ a, w a * exp (lam * (g a - ∑ z, w z * g z)) ≤
      exp (((hi - lo) / 2) ^ 2 * lam ^ 2 / 2) := by
  let μ := finiteWeightMeasure w
  letI : IsProbabilityMeasure μ := finiteWeightMeasure_isProbability w hw0 hw1
  have hmeas : AEMeasurable g μ := AEMeasurable.of_discrete
  have hmem : ∀ᵐ a ∂μ, g a ∈ Set.Icc lo hi := Filter.Eventually.of_forall hg
  have hsub := hasSubgaussianMGF_of_mem_Icc (μ := μ) hmeas hmem
  have hmgf := hsub.mgf_le lam
  rw [mgf, integral_finiteWeightMeasure w hw0] at hmgf
  rw [integral_finiteWeightMeasure w hw0] at hmgf
  have hlohi : lo ≤ hi := by
    let a : α := Classical.choice (inferInstance : Nonempty α)
    exact (hg a).1.trans (hg a).2
  simpa [μ, abs_of_nonneg (sub_nonneg.mpr hlohi)] using hmgf

/-- Hoeffding's lemma in the form useful for bounded differences: only the pairwise
oscillation of the finite random variable is specified. -/
lemma finite_weighted_hoeffding_of_pairwise (w : α → ℝ) (g : α → ℝ) (b lam : ℝ)
    (hw0 : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1) (hb : 0 ≤ b)
    (hosc : ∀ a z, |g a - g z| ≤ b) :
    ∑ a, w a * exp (lam * (g a - ∑ z, w z * g z)) ≤
      exp (b ^ 2 * lam ^ 2 / 8) := by
  let S : Finset ℝ := Finset.univ.image g
  have hS : S.Nonempty := by
    let a : α := Classical.choice (inferInstance : Nonempty α)
    exact ⟨g a, Finset.mem_image_of_mem g (Finset.mem_univ a)⟩
  let lo : ℝ := S.min' hS
  let hi : ℝ := S.max' hS
  have hgIcc : ∀ a, g a ∈ Set.Icc lo hi := by
    intro a
    exact ⟨Finset.min'_le S (g a) (Finset.mem_image_of_mem g (Finset.mem_univ a)),
      Finset.le_max' S (g a) (Finset.mem_image_of_mem g (Finset.mem_univ a))⟩
  have hwidth0 : 0 ≤ hi - lo := sub_nonneg.mpr (Finset.min'_le_max' S hS)
  have hwidth : hi - lo ≤ b := by
    obtain ⟨a, -, ha⟩ := Finset.mem_image.mp (Finset.max'_mem S hS)
    obtain ⟨z, -, hz⟩ := Finset.mem_image.mp (Finset.min'_mem S hS)
    dsimp [hi, lo]
    rw [← ha, ← hz]
    exact (le_abs_self (g a - g z)).trans (hosc a z)
  refine (finite_weighted_hoeffding w g lo hi lam hw0 hw1 hgIcc).trans ?_
  apply Real.exp_le_exp.mpr
  have hsquare : (hi - lo) ^ 2 ≤ b ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hsquare (sq_nonneg lam)
  nlinarith

/-! ## Finite product identities -/

lemma sum_fin_succ_eq {n : ℕ} {β : Type*} [AddCommMonoid β]
    (F : (Fin (n + 1) → α) → β) :
    ∑ x, F x = ∑ a : α, ∑ y : Fin n → α, F (Fin.cons a y) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) ↦ α)).sum_comp]
  exact Fintype.sum_prod_type _

@[simp] lemma productMass_cons {n : ℕ} (w : Fin (n + 1) → α → ℝ)
    (a : α) (y : Fin n → α) :
    productMass w (Fin.cons a y) =
      w 0 a * productMass (fun i z ↦ w i.succ z) y := by
  simp [productMass, Fin.prod_univ_succ]

/-- Average over the first coordinate, retaining the remaining coordinates. -/
def sectionAverage {n : ℕ} (w : Fin (n + 1) → α → ℝ)
    (f : (Fin (n + 1) → α) → ℝ) (y : Fin n → α) : ℝ :=
  ∑ a, w 0 a * f (Fin.cons a y)

lemma weightedMean_succ {n : ℕ} (w : Fin (n + 1) → α → ℝ)
    (f : (Fin (n + 1) → α) → ℝ) :
    weightedMean w f =
      weightedMean (fun i z ↦ w i.succ z) (sectionAverage w f) := by
  simp only [weightedMean, sum_fin_succ_eq, productMass_cons, sectionAverage]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma sectionAverage_boundedDiff {n : ℕ} (w : Fin (n + 1) → α → ℝ)
    (f : (Fin (n + 1) → α) → ℝ) (b : Fin (n + 1) → ℝ)
    (hw0 : ∀ i a, 0 ≤ w i a) (hw1 : ∀ i, ∑ a, w i a = 1)
    (hbd : ∀ i (x y : Fin (n + 1) → α),
      (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ b i) :
    ∀ i (x y : Fin n → α),
      (∀ j, j ≠ i → x j = y j) →
      |sectionAverage w f x - sectionAverage w f y| ≤ b i.succ := by
  intro i x y hxy
  rw [sectionAverage, sectionAverage, ← Finset.sum_sub_distrib]
  calc
    |∑ a, (w 0 a * f (Fin.cons a x) - w 0 a * f (Fin.cons a y))|
        ≤ ∑ a, |w 0 a * f (Fin.cons a x) - w 0 a * f (Fin.cons a y)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a, w 0 a * |f (Fin.cons a x) - f (Fin.cons a y)| := by
          apply Finset.sum_congr rfl
          intro a _
          rw [← mul_sub, abs_mul, abs_of_nonneg (hw0 0 a)]
    _ ≤ ∑ a, w 0 a * b i.succ := by
          apply Finset.sum_le_sum
          intro a _
          apply mul_le_mul_of_nonneg_left _ (hw0 0 a)
          apply hbd i.succ
          intro j hj
          cases j using Fin.cases with
          | zero => rfl
          | succ j =>
              exact hxy j (fun h ↦ hj (congrArg (fun k : Fin n ↦ k.succ) h))
    _ = b i.succ := by rw [← Finset.sum_mul, hw1]; simp

lemma productMass_nonneg {n : ℕ} (w : Fin n → α → ℝ)
    (hw0 : ∀ i a, 0 ≤ w i a) (x : Fin n → α) :
    0 ≤ productMass w x := by
  exact Finset.prod_nonneg fun i _ ↦ hw0 i (x i)

/-! ## Exponential moments and the tail bound -/

/-- The centered exponential-moment estimate behind McDiarmid's inequality. -/
theorem expMomentBound (n : ℕ) (w : Fin n → α → ℝ)
    (f : (Fin n → α) → ℝ) (b : Fin n → ℝ)
    (hw0 : ∀ i a, 0 ≤ w i a) (hw1 : ∀ i, ∑ a, w i a = 1)
    (hb : ∀ i, 0 ≤ b i)
    (hbd : ∀ i (x y : Fin n → α),
      (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ b i)
    (lam : ℝ) :
    ∑ x, productMass w x * exp (lam * (f x - weightedMean w f)) ≤
      exp (lam ^ 2 / 8 * ∑ i, b i ^ 2) := by
  induction n with
  | zero => simp [productMass, weightedMean]
  | succ n ih =>
      let wt : Fin n → α → ℝ := fun i a ↦ w i.succ a
      let g : (Fin n → α) → ℝ := sectionAverage w f
      let μ : ℝ := weightedMean w f
      have hmean : weightedMean wt g = μ := by
        exact (weightedMean_succ w f).symm
      have hi := ih wt g (fun i ↦ b i.succ)
        (fun i a ↦ hw0 i.succ a) (fun i ↦ hw1 i.succ) (fun i ↦ hb i.succ)
        (sectionAverage_boundedDiff w f b hw0 hw1 hbd)
      rw [hmean] at hi
      have hsection (y : Fin n → α) :
          ∑ a, w 0 a * exp (lam * (f (Fin.cons a y) - μ)) ≤
            exp (b 0 ^ 2 * lam ^ 2 / 8) * exp (lam * (g y - μ)) := by
        have hosc : ∀ a z : α,
            |f (Fin.cons a y) - f (Fin.cons z y)| ≤ b 0 := by
          intro a z
          apply hbd 0
          intro j hj
          cases j using Fin.cases with
          | zero => exact (hj rfl).elim
          | succ j => rfl
        have hh := finite_weighted_hoeffding_of_pairwise
          (w 0) (fun a ↦ f (Fin.cons a y)) (b 0) lam
          (hw0 0) (hw1 0) (hb 0) hosc
        have hfactor :
            ∑ a, w 0 a * exp (lam * (f (Fin.cons a y) - μ)) =
              exp (lam * (g y - μ)) *
                ∑ a, w 0 a * exp
                  (lam * (f (Fin.cons a y) - ∑ z, w 0 z * f (Fin.cons z y))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          have hexp :
              lam * (f (Fin.cons a y) - μ) =
                lam * (g y - μ) +
                  lam * (f (Fin.cons a y) - ∑ z, w 0 z * f (Fin.cons z y)) := by
            dsimp [g, sectionAverage]
            ring
          rw [hexp, Real.exp_add]
          ring
        rw [hfactor]
        calc
          exp (lam * (g y - μ)) *
                ∑ a, w 0 a * exp
                  (lam * (f (Fin.cons a y) - ∑ z, w 0 z * f (Fin.cons z y)))
              ≤ exp (lam * (g y - μ)) * exp (b 0 ^ 2 * lam ^ 2 / 8) :=
                mul_le_mul_of_nonneg_left hh (Real.exp_nonneg _)
          _ = exp (b 0 ^ 2 * lam ^ 2 / 8) * exp (lam * (g y - μ)) := by ring
      calc
        ∑ x, productMass w x * exp (lam * (f x - weightedMean w f))
            = ∑ y, productMass wt y *
                ∑ a, w 0 a * exp (lam * (f (Fin.cons a y) - μ)) := by
              rw [sum_fin_succ_eq, Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro y _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro a _
              rw [productMass_cons]
              dsimp [wt, μ]
              ring
        _ ≤ ∑ y, productMass wt y *
              (exp (b 0 ^ 2 * lam ^ 2 / 8) * exp (lam * (g y - μ))) := by
              apply Finset.sum_le_sum
              intro y _
              exact mul_le_mul_of_nonneg_left (hsection y)
                (productMass_nonneg wt (fun i a ↦ hw0 i.succ a) y)
        _ = exp (b 0 ^ 2 * lam ^ 2 / 8) *
              ∑ y, productMass wt y * exp (lam * (g y - μ)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro y _
              ring
        _ ≤ exp (b 0 ^ 2 * lam ^ 2 / 8) *
              exp (lam ^ 2 / 8 * ∑ i : Fin n, b i.succ ^ 2) :=
              mul_le_mul_of_nonneg_left hi (Real.exp_nonneg _)
        _ = exp (lam ^ 2 / 8 * ∑ i : Fin (n + 1), b i ^ 2) := by
              rw [← Real.exp_add, Fin.sum_univ_succ]
              congr 1
              ring

lemma sum_productMass_eq_one (n : ℕ) (w : Fin n → α → ℝ)
    (hw1 : ∀ i, ∑ a, w i a = 1) :
    ∑ x, productMass w x = 1 := by
  induction n with
  | zero => simp [productMass]
  | succ n ih =>
      rw [sum_fin_succ_eq]
      simp_rw [productMass_cons, ← Finset.mul_sum]
      rw [← Finset.sum_mul, hw1 0]
      simp only [one_mul]
      simpa using ih (fun i a ↦ w i.succ a) (fun i ↦ hw1 i.succ)

/-- Weighted mass of an event in the finite product space. -/
def eventMass {n : ℕ} (w : Fin n → α → ℝ) (E : Set (Fin n → α)) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x ↦ x ∈ E), productMass w x

lemma eventMass_univ {n : ℕ} (w : Fin n → α → ℝ)
    (hw1 : ∀ i, ∑ a, w i a = 1) :
    eventMass w Set.univ = 1 := by
  simp [eventMass, sum_productMass_eq_one n w hw1]

lemma eventMass_nonneg {n : ℕ} (w : Fin n → α → ℝ)
    (hw0 : ∀ i a, 0 ≤ w i a) (E : Set (Fin n → α)) :
    0 ≤ eventMass w E := by
  exact Finset.sum_nonneg fun x _ ↦ productMass_nonneg w hw0 x

lemma eventMass_mono {n : ℕ} (w : Fin n → α → ℝ)
    (hw0 : ∀ i a, 0 ≤ w i a) {E F : Set (Fin n → α)} (hEF : E ⊆ F) :
    eventMass w E ≤ eventMass w F := by
  unfold eventMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, hEF hx.2⟩
  · intro x _ _
    exact productMass_nonneg w hw0 x

lemma eventMass_le_one {n : ℕ} (w : Fin n → α → ℝ)
    (hw0 : ∀ i a, 0 ≤ w i a) (hw1 : ∀ i, ∑ a, w i a = 1)
    (E : Set (Fin n → α)) : eventMass w E ≤ 1 := by
  rw [← eventMass_univ w hw1]
  exact eventMass_mono w hw0 (Set.subset_univ E)

/-- The elementary union bound for the explicit finite product mass. -/
lemma eventMass_union_le {n : ℕ} (w : Fin n → α → ℝ)
    (hw0 : ∀ i a, 0 ≤ w i a) (E F : Set (Fin n → α)) :
    eventMass w (E ∪ F) ≤ eventMass w E + eventMass w F := by
  simp only [eventMass, Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  by_cases hxE : x ∈ E <;> by_cases hxF : x ∈ F <;>
    simp [hxE, hxF, productMass_nonneg w hw0 x]

/-- Finite union bound, useful for turning one McDiarmid estimate into simultaneous
control of polynomially many bad events. -/
lemma eventMass_biUnion_le_sum {n : ℕ} {ι : Type*} [DecidableEq ι]
    (w : Fin n → α → ℝ) (hw0 : ∀ i a, 0 ≤ w i a)
    (s : Finset ι) (E : ι → Set (Fin n → α)) :
    eventMass w (⋃ i ∈ s, E i) ≤ ∑ i ∈ s, eventMass w (E i) := by
  induction s using Finset.induction_on with
  | empty => simp [eventMass]
  | @insert i s his ih =>
      have hset : (⋃ j ∈ insert i s, E j) = E i ∪ ⋃ j ∈ s, E j := by
        ext x
        simp
      rw [hset, Finset.sum_insert his]
      exact (eventMass_union_le w hw0 (E i) (⋃ j ∈ s, E j)).trans
        (add_le_add (le_refl _) ih)

/-- Upper-tail McDiarmid inequality for an arbitrary normalized finite product distribution.
The positivity assumption merely excludes the degenerate all-zero bounded-difference budget. -/
theorem mcdiarmid_upper (n : ℕ) (w : Fin n → α → ℝ)
    (f : (Fin n → α) → ℝ) (b : Fin n → ℝ)
    (hw0 : ∀ i a, 0 ≤ w i a) (hw1 : ∀ i, ∑ a, w i a = 1)
    (hb : ∀ i, 0 ≤ b i)
    (hbd : ∀ i (x y : Fin n → α),
      (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ b i)
    (t : ℝ) (ht : 0 ≤ t) (hS : 0 < ∑ i, b i ^ 2) :
    eventMass w {x | weightedMean w f + t ≤ f x} ≤
      exp (-2 * t ^ 2 / ∑ i, b i ^ 2) := by
  let S : ℝ := ∑ i, b i ^ 2
  let lam : ℝ := 4 * t / S
  have hlam : 0 ≤ lam := div_nonneg (mul_nonneg (by norm_num) ht) hS.le
  have hpoint : ∀ x ∈ Finset.univ.filter
      (fun x : Fin n → α ↦ x ∈ {x | weightedMean w f + t ≤ f x}),
      productMass w x * exp (lam * t) ≤
        productMass w x * exp (lam * (f x - weightedMean w f)) := by
    intro x hx
    apply mul_le_mul_of_nonneg_left _ (productMass_nonneg w hw0 x)
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hlam
    have hevent := (Finset.mem_filter.mp hx).2
    change weightedMean w f + t ≤ f x at hevent
    linarith
  have hmarkov :
      eventMass w {x | weightedMean w f + t ≤ f x} * exp (lam * t) ≤
        ∑ x, productMass w x * exp (lam * (f x - weightedMean w f)) := by
    calc
      eventMass w {x | weightedMean w f + t ≤ f x} * exp (lam * t)
          = ∑ x ∈ Finset.univ.filter
              (fun x : Fin n → α ↦ x ∈ {x | weightedMean w f + t ≤ f x}),
                productMass w x * exp (lam * t) := by
            simp only [eventMass, Finset.sum_mul]
      _ ≤ ∑ x ∈ Finset.univ.filter
              (fun x : Fin n → α ↦ x ∈ {x | weightedMean w f + t ≤ f x}),
                productMass w x * exp (lam * (f x - weightedMean w f)) := by
            exact Finset.sum_le_sum hpoint
      _ ≤ ∑ x, productMass w x * exp (lam * (f x - weightedMean w f)) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            intro x _ _
            exact mul_nonneg (productMass_nonneg w hw0 x) (Real.exp_nonneg _)
  have hmom := expMomentBound n w f b hw0 hw1 hb hbd lam
  have hdiv : eventMass w {x | weightedMean w f + t ≤ f x} ≤
      exp (lam ^ 2 / 8 * S) / exp (lam * t) := by
    rw [le_div_iff₀ (Real.exp_pos _)]
    exact hmarkov.trans (by simpa [S] using hmom)
  calc
    eventMass w {x | weightedMean w f + t ≤ f x}
        ≤ exp (lam ^ 2 / 8 * S) / exp (lam * t) := hdiv
    _ = exp (lam ^ 2 / 8 * S - lam * t) := by rw [Real.exp_sub]
    _ = exp (-2 * t ^ 2 / ∑ i, b i ^ 2) := by
      congr 1
      dsimp [lam, S]
      field_simp
      ring

/-- Degenerate-safe upper-tail form.  When all difference bounds vanish, the event has
mass at most one, which is exactly the right-hand side under Lean's division-by-zero
convention. -/
theorem mcdiarmid_upper_all (n : ℕ) (w : Fin n → α → ℝ)
    (f : (Fin n → α) → ℝ) (b : Fin n → ℝ)
    (hw0 : ∀ i a, 0 ≤ w i a) (hw1 : ∀ i, ∑ a, w i a = 1)
    (hb : ∀ i, 0 ≤ b i)
    (hbd : ∀ i (x y : Fin n → α),
      (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ b i)
    (t : ℝ) (ht : 0 ≤ t) :
    eventMass w {x | weightedMean w f + t ≤ f x} ≤
      exp (-2 * t ^ 2 / ∑ i, b i ^ 2) := by
  have hnonneg : 0 ≤ ∑ i, b i ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  rcases hnonneg.eq_or_lt with hzero | hpos
  · have hzero' : ∑ i, b i ^ 2 = 0 := hzero.symm
    simpa [hzero'] using eventMass_le_one w hw0 hw1
      {x | weightedMean w f + t ≤ f x}
  · exact mcdiarmid_upper n w f b hw0 hw1 hb hbd t ht hpos

@[simp] lemma weightedMean_neg {n : ℕ} (w : Fin n → α → ℝ)
    (f : (Fin n → α) → ℝ) :
    weightedMean w (fun x ↦ -f x) = -weightedMean w f := by
  simp only [weightedMean, mul_neg, Finset.sum_neg_distrib]

/-- Lower-tail McDiarmid inequality. -/
theorem mcdiarmid_lower_all (n : ℕ) (w : Fin n → α → ℝ)
    (f : (Fin n → α) → ℝ) (b : Fin n → ℝ)
    (hw0 : ∀ i a, 0 ≤ w i a) (hw1 : ∀ i, ∑ a, w i a = 1)
    (hb : ∀ i, 0 ≤ b i)
    (hbd : ∀ i (x y : Fin n → α),
      (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ b i)
    (t : ℝ) (ht : 0 ≤ t) :
    eventMass w {x | f x ≤ weightedMean w f - t} ≤
      exp (-2 * t ^ 2 / ∑ i, b i ^ 2) := by
  have hbd_neg : ∀ i (x y : Fin n → α),
      (∀ j, j ≠ i → x j = y j) →
      |(-f x) - (-f y)| ≤ b i := by
    intro i x y hxy
    simpa only [neg_sub_neg, abs_neg] using
      hbd i y x (fun j hj ↦ (hxy j hj).symm)
  have h := mcdiarmid_upper_all n w (fun x ↦ -f x) b
    hw0 hw1 hb hbd_neg t ht
  have hset : {x | f x ≤ weightedMean w f - t} =
      {x | weightedMean w (fun x ↦ -f x) + t ≤ -f x} := by
    ext x
    simp only [Set.mem_ofPred_eq, weightedMean_neg]
    constructor <;> intro hx <;> linarith
  rw [hset]
  exact h

/-- Two-sided bounded-differences inequality. -/
theorem mcdiarmid_two_sided (n : ℕ) (w : Fin n → α → ℝ)
    (f : (Fin n → α) → ℝ) (b : Fin n → ℝ)
    (hw0 : ∀ i a, 0 ≤ w i a) (hw1 : ∀ i, ∑ a, w i a = 1)
    (hb : ∀ i, 0 ≤ b i)
    (hbd : ∀ i (x y : Fin n → α),
      (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ b i)
    (t : ℝ) (ht : 0 ≤ t) :
    eventMass w {x | t ≤ |f x - weightedMean w f|} ≤
      2 * exp (-2 * t ^ 2 / ∑ i, b i ^ 2) := by
  have hset : {x | t ≤ |f x - weightedMean w f|} =
      {x | weightedMean w f + t ≤ f x} ∪
        {x | f x ≤ weightedMean w f - t} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    rw [le_abs]
    constructor
    · intro h
      rcases h with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    · intro h
      rcases h with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
  rw [hset]
  calc
    eventMass w ({x | weightedMean w f + t ≤ f x} ∪
        {x | f x ≤ weightedMean w f - t})
        ≤ eventMass w {x | weightedMean w f + t ≤ f x} +
          eventMass w {x | f x ≤ weightedMean w f - t} :=
            eventMass_union_le w hw0 _ _
    _ ≤ exp (-2 * t ^ 2 / ∑ i, b i ^ 2) +
          exp (-2 * t ^ 2 / ∑ i, b i ^ 2) :=
            add_le_add (mcdiarmid_upper_all n w f b hw0 hw1 hb hbd t ht)
              (mcdiarmid_lower_all n w f b hw0 hw1 hb hbd t ht)
    _ = 2 * exp (-2 * t ^ 2 / ∑ i, b i ^ 2) := by ring

/-! ## Independent biased Bernoulli specialization -/

/-- Coordinate weights for independent Bernoulli bits, with `true` having probability `p i`. -/
def bernoulliWeight {n : ℕ} (p : Fin n → ℝ) (i : Fin n) (q : Bool) : ℝ :=
  if q then p i else 1 - p i

lemma bernoulliWeight_nonneg {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) :
    ∀ i q, 0 ≤ bernoulliWeight p i q := by
  intro i q
  cases q <;> simp [bernoulliWeight, (hp i).1, (hp i).2]

lemma bernoulliWeight_sum_one {n : ℕ} (p : Fin n → ℝ) :
    ∀ i, ∑ q : Bool, bernoulliWeight p i q = 1 := by
  intro i
  rw [Fintype.sum_bool]
  simp [bernoulliWeight]

/-- McDiarmid directly for independent biased bits.  The biases may vary by coordinate. -/
theorem bernoulli_mcdiarmid_upper (n : ℕ) (p : Fin n → ℝ)
    (f : (Fin n → Bool) → ℝ) (b : Fin n → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (hb : ∀ i, 0 ≤ b i)
    (hbd : ∀ i (x y : Fin n → Bool),
      (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ b i)
    (t : ℝ) (ht : 0 ≤ t) :
    eventMass (bernoulliWeight p) {x | weightedMean (bernoulliWeight p) f + t ≤ f x} ≤
      exp (-2 * t ^ 2 / ∑ i, b i ^ 2) := by
  exact mcdiarmid_upper_all n (bernoulliWeight p) f b
    (bernoulliWeight_nonneg p hp) (bernoulliWeight_sum_one p) hb hbd t ht

/-- Two-sided McDiarmid directly for independent biased bits. -/
theorem bernoulli_mcdiarmid_two_sided (n : ℕ) (p : Fin n → ℝ)
    (f : (Fin n → Bool) → ℝ) (b : Fin n → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (hb : ∀ i, 0 ≤ b i)
    (hbd : ∀ i (x y : Fin n → Bool),
      (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ b i)
    (t : ℝ) (ht : 0 ≤ t) :
    eventMass (bernoulliWeight p)
        {x | t ≤ |f x - weightedMean (bernoulliWeight p) f|} ≤
      2 * exp (-2 * t ^ 2 / ∑ i, b i ^ 2) := by
  exact mcdiarmid_two_sided n (bernoulliWeight p) f b
    (bernoulliWeight_nonneg p hp) (bernoulliWeight_sum_one p) hb hbd t ht

end
end Erdos703McDiarmid

