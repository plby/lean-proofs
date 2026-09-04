import ErdosProblems.Erdos88.SliceMixture

/-!
# From the slice mixture to Gaussian comparison

This file develops the weighted-coupling transfer estimates needed to combine
KSSS Lemma 11.3 with the quadratic invariance principle in Lemma 11.1.
-/

open scoped BigOperators

namespace Erdos88.BooleanSlices

open Classical Finset

namespace FiniteWeightedCoupling

variable {A B : Type*} [Fintype A] [Nonempty A]
  [Fintype B] [Nonempty B]

/-- Expectation with respect to the joint mass of a weighted coupling. -/
noncomputable def expectation (C : FiniteWeightedCoupling A B)
    (Z : A → B → ℝ) : ℝ :=
  ∑ a, ∑ b, C.weight a b * Z a b

lemma expectation_left (C : FiniteWeightedCoupling A B) (X : A → ℝ) :
    C.expectation (fun a _ ↦ X a) = uniformExpectation X := by
  rw [expectation, uniformExpectation, Fintype.expect_eq_sum_div_card]
  calc
    (∑ a, ∑ b, C.weight a b * X a) =
        ∑ a, (∑ b, C.weight a b) * X a := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [← Finset.sum_mul]
    _ = ∑ a, (1 / (Fintype.card A : ℝ)) * X a := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [C.left_sum]
    _ = (∑ a, X a) / (Fintype.card A : ℝ) := by
      rw [← Finset.mul_sum]
      ring

lemma expectation_right (C : FiniteWeightedCoupling A B) (Y : B → ℝ) :
    C.expectation (fun _ b ↦ Y b) = uniformExpectation Y := by
  rw [expectation, uniformExpectation, Fintype.expect_eq_sum_div_card,
    Finset.sum_comm]
  calc
    (∑ b, ∑ a, C.weight a b * Y b) =
        ∑ b, (∑ a, C.weight a b) * Y b := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [← Finset.sum_mul]
    _ = ∑ b, (1 / (Fintype.card B : ℝ)) * Y b := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [C.right_sum]
    _ = (∑ b, Y b) / (Fintype.card B : ℝ) := by
      rw [← Finset.mul_sum]
      ring

lemma expectation_const (C : FiniteWeightedCoupling A B) (c : ℝ) :
    C.expectation (fun _ _ ↦ c) = c := by
  rw [C.expectation_left (fun _ : A ↦ c), uniformExpectation_const]

lemma expectation_add (C : FiniteWeightedCoupling A B) (X Y : A → B → ℝ) :
    C.expectation (fun a b ↦ X a b + Y a b) =
      C.expectation X + C.expectation Y := by
  unfold expectation
  simp_rw [mul_add, Finset.sum_add_distrib]

lemma expectation_sub (C : FiniteWeightedCoupling A B) (X Y : A → B → ℝ) :
    C.expectation (fun a b ↦ X a b - Y a b) =
      C.expectation X - C.expectation Y := by
  unfold expectation
  simp_rw [mul_sub, Finset.sum_sub_distrib]

lemma expectation_const_mul (C : FiniteWeightedCoupling A B) (c : ℝ)
    (X : A → B → ℝ) :
    C.expectation (fun a b ↦ c * X a b) = c * C.expectation X := by
  unfold expectation
  simp_rw [show ∀ a b, C.weight a b * (c * X a b) =
    c * (C.weight a b * X a b) by intros; ring]
  simp_rw [← Finset.mul_sum]

lemma expectation_mono (C : FiniteWeightedCoupling A B) {X Y : A → B → ℝ}
    (h : ∀ a b, X a b ≤ Y a b) : C.expectation X ≤ C.expectation Y := by
  unfold expectation
  apply Finset.sum_le_sum
  intro a ha
  apply Finset.sum_le_sum
  intro b hb
  exact mul_le_mul_of_nonneg_left (h a b) (C.weight_nonneg a b)

lemma expectation_congr (C : FiniteWeightedCoupling A B) {X Y : A → B → ℝ}
    (h : ∀ a b, X a b = Y a b) : C.expectation X = C.expectation Y := by
  apply congrArg C.expectation
  funext a b
  exact h a b

lemma abs_expectation_le (C : FiniteWeightedCoupling A B) (X : A → B → ℝ) :
    |C.expectation X| ≤ C.expectation (fun a b ↦ |X a b|) := by
  unfold expectation
  calc
    |∑ a, ∑ b, C.weight a b * X a b| ≤
        ∑ a, |∑ b, C.weight a b * X a b| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, ∑ b, |C.weight a b * X a b| := by
      apply Finset.sum_le_sum
      intro a ha
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a, ∑ b, C.weight a b * |X a b| := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [abs_mul, abs_of_nonneg (C.weight_nonneg a b)]

lemma mass_add_compl (C : FiniteWeightedCoupling A B) (p : A → B → Prop) :
    C.mass p + C.mass (fun a b ↦ ¬ p a b) = 1 := by
  rw [← C.mass_univ]
  unfold mass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hp : p a b <;> simp [hp]

lemma bad_mass_le_of_isClose (C : FiniteWeightedCoupling A B)
    (X : A → ℝ) (Y : B → ℝ) (r q : ℝ)
    (hclose : C.IsClose X Y r q) :
    C.mass (fun a b ↦ r < |X a - Y b|) ≤ q := by
  have hpart := C.mass_add_compl (fun a b ↦ |X a - Y b| ≤ r)
  unfold IsClose at hclose
  have hbad : C.mass (fun a b ↦ ¬ |X a - Y b| ≤ r) ≤ q := by
    linarith
  simpa only [not_le] using hbad

lemma expectation_indicator_const (C : FiniteWeightedCoupling A B)
    (p : A → B → Prop) (c : ℝ) :
    C.expectation (fun a b ↦ if p a b then c else 0) = c * C.mass p := by
  unfold expectation mass
  simp_rw [show ∀ a b, C.weight a b * (if p a b then c else 0) =
      c * (if p a b then C.weight a b else 0) by
    intro a b
    by_cases hp : p a b <;> simp [hp] <;> ring]
  simp_rw [← Finset.mul_sum]

lemma expectation_abs_difference_le_of_isClose
    (C : FiniteWeightedCoupling A B) (X : A → ℝ) (Y : B → ℝ)
    (r q D : ℝ) (hr : 0 ≤ r) (hD0 : 0 ≤ D)
    (hclose : C.IsClose X Y r q)
    (hD : ∀ a b, |X a - Y b| ≤ D) :
    C.expectation (fun a b ↦ |X a - Y b|) ≤ r + D * q := by
  have hbad := C.bad_mass_le_of_isClose X Y r q hclose
  calc
    C.expectation (fun a b ↦ |X a - Y b|) ≤
        C.expectation (fun a b ↦
          r + if r < |X a - Y b| then D else 0) := by
      apply C.expectation_mono
      intro a b
      by_cases hab : r < |X a - Y b|
      · simp only [hab, if_true]
        exact (hD a b).trans (by linarith)
      · simp only [hab, if_false, add_zero]
        exact le_of_not_gt hab
    _ = r + D * C.mass (fun a b ↦ r < |X a - Y b|) := by
      rw [C.expectation_add, C.expectation_const,
        C.expectation_indicator_const]
    _ ≤ r + D * q := by gcongr

lemma expectation_sq_difference_le_of_isClose
    (C : FiniteWeightedCoupling A B) (X : A → ℝ) (Y : B → ℝ)
    (r q D : ℝ) (hr : 0 ≤ r) (hD0 : 0 ≤ D)
    (hclose : C.IsClose X Y r q)
    (hD : ∀ a b, |X a - Y b| ≤ D) :
    C.expectation (fun a b ↦ (X a - Y b) ^ 2) ≤ r ^ 2 + D ^ 2 * q := by
  have hbad := C.bad_mass_le_of_isClose X Y r q hclose
  calc
    C.expectation (fun a b ↦ (X a - Y b) ^ 2) ≤
        C.expectation (fun a b ↦
          r ^ 2 + if r < |X a - Y b| then D ^ 2 else 0) := by
      apply C.expectation_mono
      intro a b
      by_cases hab : r < |X a - Y b|
      · simp only [hab, if_true]
        have hsquare : (X a - Y b) ^ 2 ≤ D ^ 2 := by
          simpa only [sq_abs] using
            (sq_le_sq₀ (abs_nonneg _) hD0).2 (hD a b)
        linarith [sq_nonneg r]
      · simp only [hab, if_false, add_zero]
        simpa only [sq_abs] using
          (sq_le_sq₀ (abs_nonneg _) hr).2 (le_of_not_gt hab)
    _ = r ^ 2 + D ^ 2 * C.mass (fun a b ↦ r < |X a - Y b|) := by
      rw [C.expectation_add, C.expectation_const,
        C.expectation_indicator_const]
    _ ≤ r ^ 2 + D ^ 2 * q := by gcongr

lemma abs_expectation_sub_le_of_isClose
    (C : FiniteWeightedCoupling A B) (X : A → ℝ) (Y : B → ℝ)
    (r q D : ℝ) (hr : 0 ≤ r) (hD0 : 0 ≤ D)
    (hclose : C.IsClose X Y r q)
    (hD : ∀ a b, |X a - Y b| ≤ D) :
    |uniformExpectation X - uniformExpectation Y| ≤ r + D * q := by
  have hmarginal : uniformExpectation X - uniformExpectation Y =
      C.expectation (fun a b ↦ X a - Y b) := by
    rw [C.expectation_sub, C.expectation_left, C.expectation_right]
  rw [hmarginal]
  exact (C.abs_expectation_le _).trans
    (C.expectation_abs_difference_le_of_isClose X Y r q D hr hD0 hclose hD)

/-- Complex expectation with respect to the joint mass of a weighted
coupling. -/
noncomputable def complexExpectation (C : FiniteWeightedCoupling A B)
    (Z : A → B → ℂ) : ℂ :=
  ∑ a, ∑ b, (C.weight a b : ℂ) * Z a b

lemma complexExpectation_left (C : FiniteWeightedCoupling A B) (X : A → ℂ) :
    C.complexExpectation (fun a _ ↦ X a) = 𝔼 a, X a := by
  rw [complexExpectation, Fintype.expect_eq_sum_div_card]
  calc
    (∑ a, ∑ b, (C.weight a b : ℂ) * X a) =
        ∑ a, ((∑ b, C.weight a b : ℝ) : ℂ) * X a := by
      apply Finset.sum_congr rfl
      intro a ha
      refine (Finset.sum_mul Finset.univ
        (fun b ↦ (C.weight a b : ℂ)) (X a)).symm.trans ?_
      congr 1
      norm_cast
    _ = ∑ a, ((1 / (Fintype.card A : ℝ) : ℝ) : ℂ) * X a := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [C.left_sum]
    _ = (∑ a, X a) / (Fintype.card A : ℂ) := by
      rw [← Finset.mul_sum]
      push_cast
      field_simp

lemma complexExpectation_right (C : FiniteWeightedCoupling A B) (Y : B → ℂ) :
    C.complexExpectation (fun _ b ↦ Y b) = 𝔼 b, Y b := by
  rw [complexExpectation, Fintype.expect_eq_sum_div_card, Finset.sum_comm]
  calc
    (∑ b, ∑ a, (C.weight a b : ℂ) * Y b) =
        ∑ b, ((∑ a, C.weight a b : ℝ) : ℂ) * Y b := by
      apply Finset.sum_congr rfl
      intro b hb
      refine (Finset.sum_mul Finset.univ
        (fun a ↦ (C.weight a b : ℂ)) (Y b)).symm.trans ?_
      congr 1
      norm_cast
    _ = ∑ b, ((1 / (Fintype.card B : ℝ) : ℝ) : ℂ) * Y b := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [C.right_sum]
    _ = (∑ b, Y b) / (Fintype.card B : ℂ) := by
      rw [← Finset.mul_sum]
      push_cast
      field_simp

lemma complexExpectation_sub (C : FiniteWeightedCoupling A B)
    (X Y : A → B → ℂ) :
    C.complexExpectation (fun a b ↦ X a b - Y a b) =
      C.complexExpectation X - C.complexExpectation Y := by
  unfold complexExpectation
  simp_rw [mul_sub, Finset.sum_sub_distrib]

/-- The norm of a weighted complex expectation is bounded by the weighted
expectation of the pointwise norms. -/
lemma norm_complexExpectation_le (C : FiniteWeightedCoupling A B)
    (Z : A → B → ℂ) :
    ‖C.complexExpectation Z‖ ≤ C.expectation (fun a b ↦ ‖Z a b‖) := by
  unfold complexExpectation expectation
  calc
    ‖∑ a, ∑ b, (C.weight a b : ℂ) * Z a b‖ ≤
        ∑ a, ‖∑ b, (C.weight a b : ℂ) * Z a b‖ := norm_sum_le _ _
    _ ≤ ∑ a, ∑ b, ‖(C.weight a b : ℂ) * Z a b‖ := by
      apply Finset.sum_le_sum
      intro a ha
      exact norm_sum_le _ _
    _ = ∑ a, ∑ b, C.weight a b * ‖Z a b‖ := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (C.weight_nonneg a b)]

/-- Range-sensitive characteristic-function transfer for a weighted finite
coupling.  The exceptional mass keeps the factor `|τ|`, which is the form
needed in KSSS Lemma 11.1. -/
lemma norm_characteristic_sub_le_of_isClose_range
    (C : FiniteWeightedCoupling A B) (X : A → ℝ) (Y : B → ℝ)
    (r q D τ : ℝ) (hr : 0 ≤ r) (hD0 : 0 ≤ D)
    (hclose : C.IsClose X Y r q)
    (hD : ∀ a b, |X a - Y b| ≤ D) :
    ‖finiteCharacteristic X τ - finiteCharacteristic Y τ‖ ≤
      |τ| * (r + D * q) := by
  let ZX : A → ℂ := fun a ↦
    Complex.exp (Complex.I * (τ * X a : ℝ))
  let ZY : B → ℂ := fun b ↦
    Complex.exp (Complex.I * (τ * Y b : ℝ))
  have hmarginal : finiteCharacteristic X τ - finiteCharacteristic Y τ =
      C.complexExpectation (fun a b ↦ ZX a - ZY b) := by
    rw [C.complexExpectation_sub, C.complexExpectation_left,
      C.complexExpectation_right]
    rfl
  rw [hmarginal]
  calc
    ‖C.complexExpectation (fun a b ↦ ZX a - ZY b)‖ ≤
        C.expectation (fun a b ↦ ‖ZX a - ZY b‖) :=
      C.norm_complexExpectation_le _
    _ ≤ C.expectation (fun a b ↦ |τ| * |X a - Y b|) := by
      apply C.expectation_mono
      intro a b
      dsimp only [ZX, ZY]
      exact (norm_exp_I_mul_sub_exp_I_mul_le _ _).trans_eq (by
        rw [← mul_sub, abs_mul])
    _ = |τ| * C.expectation (fun a b ↦ |X a - Y b|) := by
      rw [C.expectation_const_mul]
    _ ≤ |τ| * (r + D * q) := by
      exact mul_le_mul_of_nonneg_left
        (C.expectation_abs_difference_le_of_isClose X Y r q D hr hD0 hclose hD)
        (abs_nonneg τ)

/-- Variance with respect to the joint mass of a weighted finite coupling. -/
noncomputable def variance (C : FiniteWeightedCoupling A B)
    (Z : A → B → ℝ) : ℝ :=
  C.expectation (fun a b ↦ (Z a b - C.expectation Z) ^ 2)

lemma variance_nonneg (C : FiniteWeightedCoupling A B) (Z : A → B → ℝ) :
    0 ≤ C.variance Z := by
  unfold variance expectation
  apply Finset.sum_nonneg
  intro a ha
  apply Finset.sum_nonneg
  intro b hb
  exact mul_nonneg (C.weight_nonneg a b) (sq_nonneg _)

lemma variance_eq_second_sub_sq (C : FiniteWeightedCoupling A B)
    (Z : A → B → ℝ) :
    C.variance Z = C.expectation (fun a b ↦ Z a b ^ 2) - C.expectation Z ^ 2 := by
  unfold variance
  calc
    C.expectation (fun a b ↦ (Z a b - C.expectation Z) ^ 2) =
        C.expectation (fun a b ↦
          Z a b ^ 2 - (2 * C.expectation Z) * Z a b + C.expectation Z ^ 2) := by
      apply C.expectation_congr
      intro a b
      ring
    _ = C.expectation (fun a b ↦ Z a b ^ 2) - C.expectation Z ^ 2 := by
      rw [C.expectation_add, C.expectation_sub, C.expectation_const_mul,
        C.expectation_const]
      ring

lemma variance_le_second (C : FiniteWeightedCoupling A B) (Z : A → B → ℝ) :
    C.variance Z ≤ C.expectation (fun a b ↦ Z a b ^ 2) := by
  rw [C.variance_eq_second_sub_sq]
  exact sub_le_self _ (sq_nonneg _)

/-- Weighted finite Cauchy--Schwarz inequality. -/
lemma expectation_mul_sq_le_sq_mul_sq (C : FiniteWeightedCoupling A B)
    (X Y : A → B → ℝ) :
    C.expectation (fun a b ↦ X a b * Y a b) ^ 2 ≤
      C.expectation (fun a b ↦ X a b ^ 2) *
        C.expectation (fun a b ↦ Y a b ^ 2) := by
  let f : A × B → ℝ := fun p ↦ √(C.weight p.1 p.2) * X p.1 p.2
  let g : A × B → ℝ := fun p ↦ √(C.weight p.1 p.2) * Y p.1 p.2
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset (A × B)) f g
  have hxy : (∑ p : A × B, f p * g p) =
      C.expectation (fun a b ↦ X a b * Y a b) := by
    rw [expectation, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    dsimp only [f, g]
    rw [show √(C.weight a b) * X a b *
        (√(C.weight a b) * Y a b) =
        √(C.weight a b) ^ 2 * (X a b * Y a b) by ring,
      Real.sq_sqrt (C.weight_nonneg a b)]
  have hxx : (∑ p : A × B, f p ^ 2) =
      C.expectation (fun a b ↦ X a b ^ 2) := by
    rw [expectation, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    dsimp only [f]
    rw [mul_pow, Real.sq_sqrt (C.weight_nonneg a b)]
  have hyy : (∑ p : A × B, g p ^ 2) =
      C.expectation (fun a b ↦ Y a b ^ 2) := by
    rw [expectation, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    dsimp only [g]
    rw [mul_pow, Real.sq_sqrt (C.weight_nonneg a b)]
  simpa only [hxy, hxx, hyy] using hcs

lemma variance_sub_eq (C : FiniteWeightedCoupling A B)
    (X Y : A → B → ℝ) :
    C.variance X - C.variance Y =
      C.variance (fun a b ↦ X a b - Y a b) +
        2 * C.expectation (fun a b ↦
          (Y a b - C.expectation Y) * (X a b - Y a b)) := by
  let D : A → B → ℝ := fun a b ↦ X a b - Y a b
  have hmean : C.expectation X = C.expectation Y + C.expectation D := by
    rw [show X = fun a b ↦ Y a b + D a b by
      funext a b; dsimp only [D]; ring, C.expectation_add]
  have hsecond : C.expectation (fun a b ↦ X a b ^ 2) =
      C.expectation (fun a b ↦ Y a b ^ 2) +
        2 * C.expectation (fun a b ↦ Y a b * D a b) +
          C.expectation (fun a b ↦ D a b ^ 2) := by
    calc
      C.expectation (fun a b ↦ X a b ^ 2) =
          C.expectation (fun a b ↦
            Y a b ^ 2 + 2 * (Y a b * D a b) + D a b ^ 2) := by
        apply C.expectation_congr
        intro a b
        dsimp only [D]
        ring
      _ = C.expectation (fun a b ↦ Y a b ^ 2) +
          2 * C.expectation (fun a b ↦ Y a b * D a b) +
            C.expectation (fun a b ↦ D a b ^ 2) := by
        rw [C.expectation_add, C.expectation_add,
          C.expectation_const_mul]
  have hcov : C.expectation (fun a b ↦
      (Y a b - C.expectation Y) * D a b) =
      C.expectation (fun a b ↦ Y a b * D a b) -
        C.expectation Y * C.expectation D := by
    calc
      C.expectation (fun a b ↦ (Y a b - C.expectation Y) * D a b) =
          C.expectation (fun a b ↦
            Y a b * D a b - C.expectation Y * D a b) := by
        apply C.expectation_congr
        intro a b
        ring
      _ = C.expectation (fun a b ↦ Y a b * D a b) -
          C.expectation Y * C.expectation D := by
        rw [C.expectation_sub, C.expectation_const_mul]
  change C.variance X - C.variance Y =
    C.variance D + 2 * C.expectation (fun a b ↦
      (Y a b - C.expectation Y) * D a b)
  rw [C.variance_eq_second_sub_sq, C.variance_eq_second_sub_sq,
    C.variance_eq_second_sub_sq, hmean, hsecond, hcov]
  ring

/-- Weighted `L²` comparison for variances. -/
lemma abs_variance_sub_le (C : FiniteWeightedCoupling A B)
    (X Y : A → B → ℝ) :
    |C.variance X - C.variance Y| ≤
      C.expectation (fun a b ↦ (X a b - Y a b) ^ 2) +
        2 * √(C.variance Y *
          C.expectation (fun a b ↦ (X a b - Y a b) ^ 2)) := by
  let D : A → B → ℝ := fun a b ↦ X a b - Y a b
  let K : ℝ := C.expectation (fun a b ↦
    (Y a b - C.expectation Y) * D a b)
  have hcs : K ^ 2 ≤ C.variance Y * C.expectation (fun a b ↦ D a b ^ 2) := by
    simpa only [K, D, variance] using
      C.expectation_mul_sq_le_sq_mul_sq
        (fun a b ↦ Y a b - C.expectation Y) D
  have habsK : |K| ≤ √(C.variance Y *
      C.expectation (fun a b ↦ D a b ^ 2)) := Real.abs_le_sqrt hcs
  have hvarD0 : 0 ≤ C.variance D := C.variance_nonneg D
  have hvarD : C.variance D ≤ C.expectation (fun a b ↦ D a b ^ 2) :=
    C.variance_le_second D
  rw [C.variance_sub_eq]
  change |C.variance D + 2 * K| ≤ _
  calc
    |C.variance D + 2 * K| ≤ C.variance D + 2 * |K| := by
      calc
        |C.variance D + 2 * K| ≤ |C.variance D| + |2 * K| := abs_add_le _ _
        _ = C.variance D + 2 * |K| := by
          rw [abs_of_nonneg hvarD0, abs_mul, abs_of_nonneg (by norm_num)]
    _ ≤ C.expectation (fun a b ↦ D a b ^ 2) +
        2 * √(C.variance Y * C.expectation (fun a b ↦ D a b ^ 2)) := by
      gcongr

lemma variance_left (C : FiniteWeightedCoupling A B) (X : A → ℝ) :
    C.variance (fun a _ ↦ X a) = uniformVariance X := by
  rw [C.variance_eq_second_sub_sq, uniformVariance_eq_second_sub_sq,
    C.expectation_left, C.expectation_left]

lemma variance_right (C : FiniteWeightedCoupling A B) (Y : B → ℝ) :
    C.variance (fun _ b ↦ Y b) = uniformVariance Y := by
  rw [C.variance_eq_second_sub_sq, uniformVariance_eq_second_sub_sq,
    C.expectation_right, C.expectation_right]

/-- Variance transfer expressed entirely in the public uniform marginal
quantities. -/
lemma abs_uniformVariance_sub_le (C : FiniteWeightedCoupling A B)
    (X : A → ℝ) (Y : B → ℝ) :
    |uniformVariance X - uniformVariance Y| ≤
      C.expectation (fun a b ↦ (X a - Y b) ^ 2) +
        2 * √(uniformVariance Y *
          C.expectation (fun a b ↦ (X a - Y b) ^ 2)) := by
  simpa only [C.variance_left, C.variance_right] using
    C.abs_variance_sub_le (fun a _ ↦ X a) (fun _ b ↦ Y b)

end FiniteWeightedCoupling

section WeightedQuadraticCouplingConsequences

variable {n m : ℕ}

/-- The deterministic quadratic range grows only polynomially, and hence is
eventually dominated by a small positive fraction of the Gaussian-in-log
exponent appearing in Lemma 11.3. -/
lemma eventually_ksssQuadraticDifferenceBound_le_exp_log_sq
    (d : ℝ) (hd4 : d < 1 / 4) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ksssQuadraticDifferenceBound n d ≤
        Real.exp (Real.log n ^ 2 / 16) := by
  have hlog :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop 64)
  filter_upwards [Filter.eventually_ge_atTop 4, hlog] with n hn hlog
  change (64 : ℝ) ≤ Real.log n at hlog
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn4R : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hscale : scale n (1 / 2 + 3 * d) ≤ (n : ℝ) ^ 2 := by
    calc
      scale n (1 / 2 + 3 * d) ≤ scale n 2 := by
        exact scale_mono_exponent hn1 (by linarith)
      _ = (n : ℝ) ^ 2 := by
        exact Real.rpow_natCast (n : ℝ) 2
  have hpoly : ksssQuadraticDifferenceBound n d ≤ 4 * (n : ℝ) ^ 3 := by
    unfold ksssQuadraticDifferenceBound
    calc
      2 * (n : ℝ) * scale n (1 / 2 + 3 * d) + 2 * (n : ℝ) ^ 2 ≤
          2 * (n : ℝ) * (n : ℝ) ^ 2 + 2 * (n : ℝ) ^ 2 := by
        gcongr
      _ ≤ 4 * (n : ℝ) ^ 3 := by
        nlinarith [show (1 : ℝ) ≤ n by exact_mod_cast hn1,
          sq_nonneg ((n : ℝ) - 1)]
  have hfour : 4 * (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hn4R)
      (pow_nonneg (show (0 : ℝ) ≤ n by positivity) 3)]
  have hpowexp : (n : ℝ) ^ 4 = Real.exp (4 * Real.log n) := by
    calc
      (n : ℝ) ^ 4 = Real.exp (Real.log n) ^ 4 := by rw [Real.exp_log hnR]
      _ = Real.exp (4 * Real.log n) :=
        (Real.exp_nat_mul (Real.log n) 4).symm
  calc
    ksssQuadraticDifferenceBound n d ≤ 4 * (n : ℝ) ^ 3 := hpoly
    _ ≤ (n : ℝ) ^ 4 := hfour
    _ = Real.exp (4 * Real.log n) := hpowexp
    _ ≤ Real.exp (Real.log n ^ 2 / 16) := by
      apply Real.exp_le_exp.mpr
      nlinarith

lemma ksss_exception_linear_le
    (d : ℝ) (hd : 0 < d) {n : ℕ} (hn : 1 ≤ n)
    (hD : ksssQuadraticDifferenceBound n d ≤
      Real.exp (Real.log n ^ 2 / 16)) :
    ksssQuadraticDifferenceBound n d * Real.exp (-(Real.log n) ^ 2 / 8) ≤
      scale n (3 / 4 + 4 * d) := by
  have hq0 : 0 ≤ Real.exp (-(Real.log n) ^ 2 / 8) := Real.exp_nonneg _
  calc
    ksssQuadraticDifferenceBound n d * Real.exp (-(Real.log n) ^ 2 / 8) ≤
        Real.exp (Real.log n ^ 2 / 16) *
          Real.exp (-(Real.log n) ^ 2 / 8) :=
      mul_le_mul_of_nonneg_right hD hq0
    _ = Real.exp (-(Real.log n) ^ 2 / 16) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (Real.log n)])
    _ ≤ scale n (3 / 4 + 4 * d) := by
      exact Real.one_le_rpow (by exact_mod_cast hn) (by linarith)

lemma ksss_exception_sq_le
    (d : ℝ) (hd : 0 < d) {n : ℕ} (hn : 1 ≤ n)
    (hD : ksssQuadraticDifferenceBound n d ≤
      Real.exp (Real.log n ^ 2 / 16)) :
    ksssQuadraticDifferenceBound n d ^ 2 *
        Real.exp (-(Real.log n) ^ 2 / 8) ≤
      scale n (3 / 4 + 4 * d) ^ 2 := by
  have hD0 := ksssQuadraticDifferenceBound_nonneg n d
  have hsq : ksssQuadraticDifferenceBound n d ^ 2 ≤
      Real.exp (Real.log n ^ 2 / 16) ^ 2 := by gcongr
  have hq0 : 0 ≤ Real.exp (-(Real.log n) ^ 2 / 8) := Real.exp_nonneg _
  have hr : 1 ≤ scale n (3 / 4 + 4 * d) :=
    Real.one_le_rpow (by exact_mod_cast hn) (by linarith)
  calc
    ksssQuadraticDifferenceBound n d ^ 2 *
        Real.exp (-(Real.log n) ^ 2 / 8) ≤
        Real.exp (Real.log n ^ 2 / 16) ^ 2 *
          Real.exp (-(Real.log n) ^ 2 / 8) :=
      mul_le_mul_of_nonneg_right hsq hq0
    _ = 1 := by
      rw [show Real.exp (Real.log n ^ 2 / 16) ^ 2 =
          Real.exp (Real.log n ^ 2 / 8) by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring,
        ← Real.exp_add]
      rw [show Real.log n ^ 2 / 8 + -(Real.log n) ^ 2 / 8 = 0 by ring,
        Real.exp_zero]
    _ ≤ scale n (3 / 4 + 4 * d) ^ 2 := by nlinarith

/-- Exact mean consequence of a weighted slice-to-Rademacher coupling. -/
lemma productSlice_mean_error_of_weightedCoupling
    (P : BucketPartition (Fin n) (Fin m)) (ell : Fin m → ℕ)
    [Nonempty (ProductSlicePoint P ell)]
    (f₀ : ℝ) (f : Fin n → ℝ) (F : Fin n → Fin n → ℝ) (δ r q : ℝ)
    (hr : 0 ≤ r)
    (hf : ∀ i, |f i| ≤ scale n (1 / 2 + 3 * δ))
    (hF : ∀ i j, |F i j| ≤ 1)
    (C : FiniteWeightedCoupling (ProductSlicePoint P ell) (Finset (Fin n)))
    (hclose : C.IsClose (productSliceQuadratic P ell f₀ f F)
      (sliceQuadratic f₀ f F) r q) :
    |uniformExpectation (productSliceQuadratic P ell f₀ f F) -
        (f₀ + trace F)| ≤
      r + ksssQuadraticDifferenceBound n δ * q := by
  have hD : ∀ x y,
      |productSliceQuadratic P ell f₀ f F x - sliceQuadratic f₀ f F y| ≤
        ksssQuadraticDifferenceBound n δ := by
    intro x y
    simpa only [productSliceQuadratic, ksssQuadraticDifferenceBound,
      mul_one] using
      (abs_sliceQuadratic_sub_le f₀ f F 1
        (scale n (1 / 2 + 3 * δ)) (by norm_num)
        (scale_nonneg n _) hf hF x.1 y)
  calc
    |uniformExpectation (productSliceQuadratic P ell f₀ f F) -
        (f₀ + trace F)| =
        |uniformExpectation (productSliceQuadratic P ell f₀ f F) -
          uniformExpectation (sliceQuadratic f₀ f F)| := by
      rw [rademacher_sliceQuadratic_mean]
    _ ≤ r + ksssQuadraticDifferenceBound n δ * q :=
      C.abs_expectation_sub_le_of_isClose _ _ r q
        (ksssQuadraticDifferenceBound n δ) hr
        (ksssQuadraticDifferenceBound_nonneg n δ) hclose hD

lemma productSlice_mean_error_ksss_of_weightedCoupling
    (P : BucketPartition (Fin n) (Fin m)) (ell : Fin m → ℕ)
    [Nonempty (ProductSlicePoint P ell)]
    (f₀ : ℝ) (f : Fin n → ℝ) (F : Fin n → Fin n → ℝ) (δ q : ℝ)
    (hf : ∀ i, |f i| ≤ scale n (1 / 2 + 3 * δ))
    (hF : ∀ i j, |F i j| ≤ 1)
    (C : FiniteWeightedCoupling (ProductSlicePoint P ell) (Finset (Fin n)))
    (hclose : C.IsClose (productSliceQuadratic P ell f₀ f F)
      (sliceQuadratic f₀ f F) (scale n (3 / 4 + 4 * δ)) q)
    (hexception : ksssQuadraticDifferenceBound n δ * q ≤
      scale n (3 / 4 + 4 * δ)) :
    |uniformExpectation (productSliceQuadratic P ell f₀ f F) -
        (f₀ + trace F)| ≤ 2 * scale n (3 / 4 + 4 * δ) := by
  have h := productSlice_mean_error_of_weightedCoupling P ell f₀ f F δ
    (scale n (3 / 4 + 4 * δ)) q (scale_nonneg _ _) hf hF C hclose
  linarith

/-- Exact variance consequence of a weighted slice-to-Rademacher coupling. -/
lemma productSlice_variance_error_of_weightedCoupling
    (P : BucketPartition (Fin n) (Fin m)) (ell : Fin m → ℕ)
    [Nonempty (ProductSlicePoint P ell)]
    (f₀ : ℝ) (f : Fin n → ℝ) (F : Fin n → Fin n → ℝ) (δ r q : ℝ)
    (hr : 0 ≤ r) (hq : 0 ≤ q)
    (hFsymm : ∀ i j, F i j = F j i)
    (hf : ∀ i, |f i| ≤ scale n (1 / 2 + 3 * δ))
    (hF : ∀ i j, |F i j| ≤ 1)
    (C : FiniteWeightedCoupling (ProductSlicePoint P ell) (Finset (Fin n)))
    (hclose : C.IsClose (productSliceQuadratic P ell f₀ f F)
      (sliceQuadratic f₀ f F) r q) :
    |uniformVariance (productSliceQuadratic P ell f₀ f F) -
        (2 * frobeniusSq F + vectorSqNorm f)| ≤
      (r ^ 2 + ksssQuadraticDifferenceBound n δ ^ 2 * q) +
        2 * √((2 * frobeniusSq F + vectorSqNorm f) *
          (r ^ 2 + ksssQuadraticDifferenceBound n δ ^ 2 * q)) + 2 * n := by
  let X : ProductSlicePoint P ell → ℝ := productSliceQuadratic P ell f₀ f F
  let Y : Finset (Fin n) → ℝ := sliceQuadratic f₀ f F
  let D : ℝ := ksssQuadraticDifferenceBound n δ
  let E₂ : ℝ := r ^ 2 + D ^ 2 * q
  have hD0 : 0 ≤ D := ksssQuadraticDifferenceBound_nonneg n δ
  have hE₂0 : 0 ≤ E₂ := by dsimp only [E₂]; positivity
  have hD : ∀ x y, |X x - Y y| ≤ D := by
    intro x y
    dsimp only [X, Y, D]
    simpa only [productSliceQuadratic, ksssQuadraticDifferenceBound,
      mul_one] using
      (abs_sliceQuadratic_sub_le f₀ f F 1
        (scale n (1 / 2 + 3 * δ)) (by norm_num)
        (scale_nonneg n _) hf hF x.1 y)
  have hsecond : C.expectation (fun x y ↦ (X x - Y y) ^ 2) ≤ E₂ := by
    exact C.expectation_sq_difference_le_of_isClose X Y r q D hr hD0 hclose hD
  have hsecond0 : 0 ≤ C.expectation (fun x y ↦ (X x - Y y) ^ 2) := by
    unfold FiniteWeightedCoupling.expectation
    apply Finset.sum_nonneg
    intro x hx
    apply Finset.sum_nonneg
    intro y hy
    exact mul_nonneg (C.weight_nonneg x y) (sq_nonneg _)
  have htarget0 : 0 ≤ 2 * frobeniusSq F + vectorSqNorm f := by
    unfold frobeniusSq vectorSqNorm
    positivity
  have hYtarget : uniformVariance Y ≤
      2 * frobeniusSq F + vectorSqNorm f := by
    rw [show Y = sliceQuadratic f₀ f F by rfl,
      rademacher_sliceQuadratic_variance_symmetric f₀ f F hFsymm]
    have hdiag : 0 ≤ ∑ i, F i i ^ 2 := by positivity
    linarith
  have hsame := C.abs_uniformVariance_sub_le X Y
  have hsqrt :
      √(uniformVariance Y * C.expectation (fun x y ↦ (X x - Y y) ^ 2)) ≤
        √((2 * frobeniusSq F + vectorSqNorm f) * E₂) := by
    apply Real.sqrt_le_sqrt
    exact mul_le_mul hYtarget hsecond hsecond0 htarget0
  have hXY : |uniformVariance X - uniformVariance Y| ≤
      E₂ + 2 * √((2 * frobeniusSq F + vectorSqNorm f) * E₂) := by
    exact hsame.trans
      (add_le_add hsecond (mul_le_mul_of_nonneg_left hsqrt (by norm_num)))
  have hdiag := abs_rademacherVariance_sub_gaussianVariance_le
    f₀ f F hFsymm hF
  change |uniformVariance X - (2 * frobeniusSq F + vectorSqNorm f)| ≤ _
  calc
    |uniformVariance X - (2 * frobeniusSq F + vectorSqNorm f)| ≤
        |uniformVariance X - uniformVariance Y| +
          |uniformVariance Y - (2 * frobeniusSq F + vectorSqNorm f)| := by
      rw [show uniformVariance X - (2 * frobeniusSq F + vectorSqNorm f) =
        (uniformVariance X - uniformVariance Y) +
          (uniformVariance Y - (2 * frobeniusSq F + vectorSqNorm f)) by ring]
      exact abs_add_le _ _
    _ ≤ E₂ + 2 * √((2 * frobeniusSq F + vectorSqNorm f) * E₂) +
        2 * n := by
      gcongr

/-- Source-exponent form of the weighted variance transfer in KSSS
Lemma 11.1. -/
lemma productSlice_variance_error_ksss_of_weightedCoupling
    (P : BucketPartition (Fin n) (Fin m)) (ell : Fin m → ℕ)
    [Nonempty (ProductSlicePoint P ell)]
    (f₀ : ℝ) (f : Fin n → ℝ) (F : Fin n → Fin n → ℝ) (δ q : ℝ)
    (hδ0 : 0 ≤ δ) (hδ : δ < 1 / 4) (hn : 1 ≤ n) (hq : 0 ≤ q)
    (hFsymm : ∀ i j, F i j = F j i)
    (hf : ∀ i, |f i| ≤ scale n (1 / 2 + 3 * δ))
    (hF : ∀ i j, |F i j| ≤ 1)
    (C : FiniteWeightedCoupling (ProductSlicePoint P ell) (Finset (Fin n)))
    (hclose : C.IsClose (productSliceQuadratic P ell f₀ f F)
      (sliceQuadratic f₀ f F) (scale n (3 / 4 + 4 * δ)) q)
    (hexception : ksssQuadraticDifferenceBound n δ ^ 2 * q ≤
      scale n (3 / 4 + 4 * δ) ^ 2) :
    |uniformVariance (productSliceQuadratic P ell f₀ f F) -
        (2 * frobeniusSq F + vectorSqNorm f)| ≤
      10 * scale n (7 / 4 + 7 * δ) := by
  let r : ℝ := scale n (3 / 4 + 4 * δ)
  let E₂ : ℝ := r ^ 2 + ksssQuadraticDifferenceBound n δ ^ 2 * q
  let T : ℝ := scale n (2 + 6 * δ)
  let S : ℝ := scale n (7 / 4 + 7 * δ)
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hr0 : 0 ≤ r := scale_nonneg _ _
  have hE₂0 : 0 ≤ E₂ := by
    dsimp only [E₂]
    exact add_nonneg (sq_nonneg r) (mul_nonneg (sq_nonneg _) hq)
  have hT0 : 0 ≤ T := by dsimp only [T]; exact scale_nonneg n _
  have hS0 : 0 ≤ S := by dsimp only [S]; exact scale_nonneg n _
  have hE₂ : E₂ ≤ 2 * r ^ 2 := by dsimp only [E₂]; linarith
  have htarget : 2 * frobeniusSq F + vectorSqNorm f ≤ 3 * T :=
    gaussianVarianceTarget_le_ksss δ hδ0 hn f F hf hF
  have hrSq : r ^ 2 = scale n (3 / 2 + 8 * δ) := by
    dsimp only [r]
    rw [scale_sq (Nat.zero_le n)]
    congr 1
    ring
  have hrSq_le_S : r ^ 2 ≤ S := by
    rw [hrSq]
    apply scale_mono_exponent hn
    linarith
  have hE₂S : E₂ ≤ 2 * S := hE₂.trans (by gcongr)
  have hTS : T * r ^ 2 = S ^ 2 := by
    rw [hrSq]
    calc
      T * scale n (3 / 2 + 8 * δ) =
          scale n ((2 + 6 * δ) + (3 / 2 + 8 * δ)) := scale_mul hnpos _ _
      _ = scale n ((7 / 4 + 7 * δ) * 2) := by congr 1 <;> ring
      _ = S ^ 2 := by symm; exact scale_sq (Nat.zero_le n) _
  have hproduct :
      (2 * frobeniusSq F + vectorSqNorm f) * E₂ ≤ 6 * S ^ 2 := by
    calc
      (2 * frobeniusSq F + vectorSqNorm f) * E₂ ≤
          (3 * T) * (2 * r ^ 2) := by
        exact mul_le_mul htarget hE₂ hE₂0 (mul_nonneg (by norm_num) hT0)
      _ = 6 * S ^ 2 := by rw [← hTS]; ring
  have hsqrt : √((2 * frobeniusSq F + vectorSqNorm f) * E₂) ≤ 3 * S := by
    rw [Real.sqrt_le_iff]
    constructor
    · exact mul_nonneg (by norm_num) hS0
    · calc
        (2 * frobeniusSq F + vectorSqNorm f) * E₂ ≤ 6 * S ^ 2 := hproduct
        _ ≤ (3 * S) ^ 2 := by nlinarith [sq_nonneg S]
  have hnS : (n : ℝ) ≤ S := by
    change (n : ℝ) ≤ Real.rpow (n : ℝ) (7 / 4 + 7 * δ)
    calc
      (n : ℝ) = Real.rpow (n : ℝ) 1 := (Real.rpow_one (n : ℝ)).symm
      _ ≤ Real.rpow (n : ℝ) (7 / 4 + 7 * δ) :=
        Real.rpow_le_rpow_of_exponent_le
          (show (1 : ℝ) ≤ (n : ℝ) by exact_mod_cast hn) (by linarith)
  have hbase := productSlice_variance_error_of_weightedCoupling
    P ell f₀ f F δ r q hr0 hq hFsymm hf hF C hclose
  change |uniformVariance (productSliceQuadratic P ell f₀ f F) -
      (2 * frobeniusSq F + vectorSqNorm f)| ≤ 10 * S
  exact hbase.trans (by
    change E₂ + 2 * √((2 * frobeniusSq F + vectorSqNorm f) * E₂) +
      2 * n ≤ 10 * S
    linarith)

end WeightedQuadraticCouplingConsequences

section GaussianDiagonalCorrection

open Invariance MeasureTheory ProbabilityTheory

variable {n : ℕ}

/-- The part lost when a full Gaussian quadratic is multilinearized. -/
def gaussianDiagonalCorrection (F : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) : ℝ :=
  ∑ i, F i i * (x i ^ 2 - 1)

def gaussianCoordinateCorrection (F : Fin n → Fin n → ℝ)
    (i : Fin n) (x : ℝ) : ℝ := F i i * (x ^ 2 - 1)

lemma gaussianDiagonalCorrection_eq_sum_coordinate
    (F : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    gaussianDiagonalCorrection F x =
      ∑ i, gaussianCoordinateCorrection F i (x i) := rfl

/-- A full quadratic is its multilinearization plus the centered diagonal
correction. -/
lemma quadraticPolynomial_eq_multilinear_add_diagonal
    (f₀ : ℝ) (f : Fin n → ℝ) (F : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) :
    quadraticPolynomial f₀ f F x =
      (toQuadraticCoeffs f₀ f F).eval x + gaussianDiagonalCorrection F x := by
  rw [toQuadraticCoeffs_eval, quadraticPolynomial]
  have hquad : quadraticPart F x = trace F +
      ∑ i, ∑ j ∈ Finset.univ.filter (i < ·),
        (F i j + F j i) * x i * x j + gaussianDiagonalCorrection F x := by
    rw [quadraticPart,
      sum_ordered_eq_trace_add_upper (fun i j ↦ x i * F i j * x j)]
    unfold gaussianDiagonalCorrection trace
    have hdiag : (∑ i, x i * F i i * x i) =
        (∑ i, F i i) + ∑ i, F i i * (x i ^ 2 - 1) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    have hoff :
        (∑ i, ∑ j ∈ Finset.univ.filter (i < ·),
          (x i * F i j * x j + x j * F j i * x i)) =
        ∑ i, ∑ j ∈ Finset.univ.filter (i < ·),
          (F i j + F j i) * x i * x j := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hdiag, hoff]
    ring
  rw [hquad]
  ring

lemma gaussianCoordinateCorrection_integrable_sq
    (F : Fin n → Fin n → ℝ) (i : Fin n) :
    Integrable (fun x : ℝ ↦ gaussianCoordinateCorrection F i x ^ 2)
      standardGaussian := by
  have hpoly : Integrable (fun x : ℝ ↦ x ^ 4 - 2 * x ^ 2 + 1)
      standardGaussian :=
    ((integrable_pow_standardGaussian 4).sub
      ((integrable_pow_standardGaussian 2).const_mul 2)).add (integrable_const 1)
  have hscaled := hpoly.const_mul (F i i ^ 2)
  exact hscaled.congr (Filter.Eventually.of_forall fun x ↦ by
    unfold gaussianCoordinateCorrection
    ring)

lemma gaussianCoordinateCorrection_memLp_two
    (F : Fin n → Fin n → ℝ) (i : Fin n) :
    MemLp (gaussianCoordinateCorrection F i) 2 standardGaussian := by
  apply (memLp_two_iff_integrable_sq (by
    change AEStronglyMeasurable
      (fun x : ℝ ↦ F i i * (x ^ 2 - 1)) standardGaussian
    fun_prop)).2
  exact gaussianCoordinateCorrection_integrable_sq F i

lemma integral_gaussianCoordinateCorrection
    (F : Fin n → Fin n → ℝ) (i : Fin n) :
    ∫ x, gaussianCoordinateCorrection F i x ∂standardGaussian = 0 := by
  unfold gaussianCoordinateCorrection
  rw [integral_const_mul]
  have hsub : Integrable (fun x : ℝ ↦ x ^ 2 - 1) standardGaussian :=
    (integrable_pow_standardGaussian 2).sub (integrable_const 1)
  rw [integral_sub (integrable_pow_standardGaussian 2) (integrable_const 1),
    standardGaussian_moment_two]
  simp

lemma integral_sq_gaussianCoordinateCorrection
    (F : Fin n → Fin n → ℝ) (i : Fin n) :
    ∫ x, gaussianCoordinateCorrection F i x ^ 2 ∂standardGaussian =
      2 * F i i ^ 2 := by
  have hpoly : Integrable (fun x : ℝ ↦ x ^ 4 - 2 * x ^ 2 + 1)
      standardGaussian :=
    ((integrable_pow_standardGaussian 4).sub
      ((integrable_pow_standardGaussian 2).const_mul 2)).add (integrable_const 1)
  calc
    (∫ x, gaussianCoordinateCorrection F i x ^ 2 ∂standardGaussian) =
        ∫ x, F i i ^ 2 * (x ^ 4 - 2 * x ^ 2 + 1) ∂standardGaussian := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by
        unfold gaussianCoordinateCorrection
        ring
    _ = F i i ^ 2 * ∫ x, (x ^ 4 - 2 * x ^ 2 + 1) ∂standardGaussian := by
      rw [integral_const_mul]
    _ = 2 * F i i ^ 2 := by
      have hadd : (∫ x : ℝ, (x ^ 4 - 2 * x ^ 2) + 1 ∂standardGaussian) =
          (∫ x : ℝ, x ^ 4 - 2 * x ^ 2 ∂standardGaussian) +
            ∫ _x : ℝ, 1 ∂standardGaussian := by
        convert integral_add
          ((integrable_pow_standardGaussian 4).sub
            ((integrable_pow_standardGaussian 2).const_mul 2))
          (integrable_const 1) using 1 <;> rfl
      have hsub : (∫ x : ℝ, x ^ 4 - 2 * x ^ 2 ∂standardGaussian) =
          (∫ x : ℝ, x ^ 4 ∂standardGaussian) -
            ∫ x : ℝ, 2 * x ^ 2 ∂standardGaussian := by
        convert integral_sub
          (integrable_pow_standardGaussian 4)
          ((integrable_pow_standardGaussian 2).const_mul 2) using 1 <;> rfl
      rw [hadd, hsub,
        integral_const_mul, standardGaussian_moment_four,
        standardGaussian_moment_two]
      simp
      ring

lemma variance_gaussianCoordinateCorrection
    (F : Fin n → Fin n → ℝ) (i : Fin n) :
    Var[gaussianCoordinateCorrection F i; standardGaussian] =
      2 * F i i ^ 2 := by
  rw [variance_of_integral_eq_zero
    (gaussianCoordinateCorrection_memLp_two F i).aemeasurable
    (integral_gaussianCoordinateCorrection F i),
    integral_sq_gaussianCoordinateCorrection]

lemma gaussianDiagonalCorrection_memLp_two
    (F : Fin n → Fin n → ℝ) :
    MemLp (gaussianDiagonalCorrection F) 2 (gaussianProductMeasure n) := by
  have hcoord : ∀ i : Fin n,
      MemLp (fun x : Fin n → ℝ ↦ gaussianCoordinateCorrection F i (x i)) 2
        (gaussianProductMeasure n) := by
    intro i
    apply (memLp_two_iff_integrable_sq (by
      change AEStronglyMeasurable
        (fun x : Fin n → ℝ ↦ F i i * (x i ^ 2 - 1))
        (gaussianProductMeasure n)
      exact (measurable_const.mul
        ((measurable_pi_apply i).pow_const 2 |>.sub measurable_const)).aestronglyMeasurable)).2
    simpa only [gaussianProductMeasure] using
      (integrable_comp_eval
        (μ := fun _i : Fin n ↦ standardGaussian) (i := i)
        (gaussianCoordinateCorrection_integrable_sq F i))
  convert memLp_finsetSum' (Finset.univ : Finset (Fin n))
    (fun i _ ↦ hcoord i) using 1
  funext x
  simp only [Finset.sum_apply]
  rfl

lemma integral_gaussianDiagonalCorrection
    (F : Fin n → Fin n → ℝ) :
    ∫ x, gaussianDiagonalCorrection F x ∂gaussianProductMeasure n = 0 := by
  have hcoord : ∀ i : Fin n, Integrable
      (fun x : Fin n → ℝ ↦ gaussianCoordinateCorrection F i (x i))
      (gaussianProductMeasure n) := by
    intro i
    unfold gaussianProductMeasure
    exact integrable_comp_eval
      ((gaussianCoordinateCorrection_memLp_two F i).integrable (by norm_num))
  rw [show gaussianDiagonalCorrection F = fun x ↦
      ∑ i, gaussianCoordinateCorrection F i (x i) by funext x; rfl,
    integral_finset_sum Finset.univ (fun i _ ↦ hcoord i)]
  apply Finset.sum_eq_zero
  intro i hi
  unfold gaussianProductMeasure
  rw [integral_comp_eval
    (gaussianCoordinateCorrection_memLp_two F i).aestronglyMeasurable,
    integral_gaussianCoordinateCorrection]

lemma integral_sq_gaussianDiagonalCorrection
    (F : Fin n → Fin n → ℝ) :
    ∫ x, gaussianDiagonalCorrection F x ^ 2 ∂gaussianProductMeasure n =
      2 * ∑ i, F i i ^ 2 := by
  have hvar := variance_sum_pi
    (μ := fun _i : Fin n ↦ standardGaussian)
    (X := fun i ↦ gaussianCoordinateCorrection F i)
    (fun i ↦ gaussianCoordinateCorrection_memLp_two F i)
  have hvar' : Var[gaussianDiagonalCorrection F; gaussianProductMeasure n] =
      ∑ i, Var[gaussianCoordinateCorrection F i; standardGaussian] := by
    have hfun : gaussianDiagonalCorrection F =
        ∑ i, fun x : Fin n → ℝ ↦ gaussianCoordinateCorrection F i (x i) := by
      funext x
      simp only [Finset.sum_apply]
      rfl
    rw [hfun]
    exact hvar
  rw [variance_of_integral_eq_zero
      (gaussianDiagonalCorrection_memLp_two F).aemeasurable
      (integral_gaussianDiagonalCorrection F)] at hvar'
  simp_rw [variance_gaussianCoordinateCorrection] at hvar'
  calc
    (∫ x, gaussianDiagonalCorrection F x ^ 2 ∂gaussianProductMeasure n) =
        ∑ i, 2 * F i i ^ 2 := hvar'
    _ = 2 * ∑ i, F i i ^ 2 :=
      (Finset.mul_sum Finset.univ (fun i ↦ F i i ^ 2) 2).symm

/-- The centered Gaussian diagonal has `L¹` norm at most its exact `L²`
norm. -/
lemma integral_abs_gaussianDiagonalCorrection_le
    (F : Fin n → Fin n → ℝ) :
    ∫ x, |gaussianDiagonalCorrection F x| ∂gaussianProductMeasure n ≤
      √(2 * ∑ i, F i i ^ 2) := by
  have hD : MemLp (gaussianDiagonalCorrection F)
      (ENNReal.ofReal (2 : ℝ)) (gaussianProductMeasure n) := by
    norm_num
    exact gaussianDiagonalCorrection_memLp_two F
  have hOne : MemLp (fun _x : Fin n → ℝ ↦ (1 : ℝ))
      (ENNReal.ofReal (2 : ℝ)) (gaussianProductMeasure n) := by
    norm_num
    exact memLp_const 1
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    Real.HolderConjugate.two_two
    hD hOne
  have hsecond := integral_sq_gaussianDiagonalCorrection F
  calc
    (∫ x, |gaussianDiagonalCorrection F x| ∂gaussianProductMeasure n) =
        ∫ x, ‖gaussianDiagonalCorrection F x‖ * ‖(1 : ℝ)‖
          ∂gaussianProductMeasure n := by simp [Real.norm_eq_abs]
    _ ≤ (∫ x, ‖gaussianDiagonalCorrection F x‖ ^ (2 : ℝ)
          ∂gaussianProductMeasure n) ^ (1 / (2 : ℝ)) *
        (∫ _x : Fin n → ℝ, ‖(1 : ℝ)‖ ^ (2 : ℝ)
          ∂gaussianProductMeasure n) ^ (1 / (2 : ℝ)) := hholder
    _ = √(2 * ∑ i, F i i ^ 2) := by
      rw [show (∫ x, ‖gaussianDiagonalCorrection F x‖ ^ (2 : ℝ)
          ∂gaussianProductMeasure n) = 2 * ∑ i, F i i ^ 2 by
        simpa only [Real.norm_eq_abs, Real.rpow_two, sq_abs] using hsecond]
      simp [integral_const, measureReal_def, Real.sqrt_eq_rpow]

/-- The `Bool`-function and positive-coordinate-set presentations of the
uniform Rademacher cube give the same expectation. -/
lemma rademacherExpectation_eq_uniformFinset
    (g : (Fin n → ℝ) → ℝ) :
    rademacherExpectation g =
      uniformExpectation (fun S : Finset (Fin n) ↦ g (signOfSet S)) := by
  let e : (Fin n → Bool) ≃ Finset (Fin n) := boolFunEquivFinset
  have hsign (x : Fin n → Bool) :
      (fun i ↦ rademacherSign (x i)) = signOfSet (e x) := by
    funext i
    cases hxi : x i <;>
      simp [e, boolFunEquivFinset, signOfSet, rademacherSign, hxi]
  unfold rademacherExpectation Invariance.finiteExpectation uniformExpectation
  rw [Fintype.expect_eq_sum_div_card]
  have hsum : (∑ x : Fin n → Bool,
      g fun i ↦ rademacherSign (x i)) =
      ∑ S : Finset (Fin n), g (signOfSet S) := by
    calc
      (∑ x : Fin n → Bool, g fun i ↦ rademacherSign (x i)) =
          ∑ x : Fin n → Bool, g (signOfSet (e x)) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [hsign]
      _ = ∑ S : Finset (Fin n), g (signOfSet S) :=
        e.sum_comp (fun S ↦ g (signOfSet S))
  rw [hsum, Fintype.card_congr e]

lemma finiteCharacteristic_eq_cos_sin
    (X : Finset (Fin n) → ℝ) (τ : ℝ) :
    finiteCharacteristic X τ =
      (uniformExpectation (fun S ↦ Real.cos (τ * X S)) : ℂ) +
        (uniformExpectation (fun S ↦ Real.sin (τ * X S)) : ℂ) * Complex.I := by
  unfold finiteCharacteristic uniformExpectation
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card,
    Fintype.expect_eq_sum_div_card]
  have hexp (S : Finset (Fin n)) :
      Complex.exp (Complex.I * (τ * X S : ℝ)) =
        (Real.cos (τ * X S) : ℂ) +
          (Real.sin (τ * X S) : ℂ) * Complex.I := by
    rw [show Complex.I * (τ * X S : ℝ) =
        ((τ * X S : ℝ) : ℂ) * Complex.I by
      push_cast
      ring,
      Complex.exp_ofReal_mul_I]
  simp_rw [hexp]
  rw [Finset.sum_add_distrib]
  rw [← Finset.sum_mul]
  push_cast
  ring

/-- Characteristic function of the full (not multilinearized) Gaussian
quadratic, represented by its real and imaginary expectations. -/
noncomputable def gaussianQuadraticCharacteristic
    (f₀ : ℝ) (f : Fin n → ℝ) (F : Fin n → Fin n → ℝ) (τ : ℝ) : ℂ :=
  (gaussianExpectation (fun x ↦
      Real.cos (τ * quadraticPolynomial f₀ f F x)) : ℂ) +
    (gaussianExpectation (fun x ↦
      Real.sin (τ * quadraticPolynomial f₀ f F x)) : ℂ) * Complex.I

lemma cos_slice_to_multilinearGaussian_le
    (δ : ℝ) (hδ : 0 ≤ δ) (hn : 1 ≤ n)
    (f₀ : ℝ) (f : Fin n → ℝ) (F : Fin n → Fin n → ℝ)
    (hf : ∀ i, |f i| ≤ scale n (1 / 2 + 3 * δ))
    (hF : ∀ i j, |F i j| ≤ 1) (τ : ℝ) :
    |uniformExpectation (fun S : Finset (Fin n) ↦
        Real.cos (τ * sliceQuadratic f₀ f F S)) -
      gaussianExpectation (fun x ↦
        Real.cos (τ * (toQuadraticCoeffs f₀ f F).eval x))| ≤
      (675 / 4 : ℝ) * |τ| ^ 4 * scale n (3 + 12 * δ) := by
  let q := toQuadraticCoeffs f₀ f F
  let qs := scaleQuadraticCoeffs τ q
  have hinv := quadratic_invariance qs isBoundedC4Test_cos
  have hrademacher : rademacherExpectation (fun x ↦ Real.cos (qs.eval x)) =
      uniformExpectation (fun S : Finset (Fin n) ↦
        Real.cos (τ * sliceQuadratic f₀ f F S)) := by
    rw [rademacherExpectation_eq_uniformFinset]
    apply uniformExpectation_congr
    intro S
    dsimp only [qs]
    rw [scaleQuadraticCoeffs_eval, toQuadraticCoeffs_eval_signOfSet]
  have hgaussian : gaussianExpectation (fun x ↦ Real.cos (qs.eval x)) =
      gaussianExpectation (fun x ↦
        Real.cos (τ * (toQuadraticCoeffs f₀ f F).eval x)) := by
    apply congrArg gaussianExpectation
    funext x
    dsimp only [qs, q]
    rw [scaleQuadraticCoeffs_eval]
  rw [hrademacher, hgaussian,
    scaleQuadraticCoeffs_sum_influence_sq] at hinv
  have hsum : (∑ i, q.influence i ^ 2) ≤
      25 * scale n (3 + 12 * δ) := by
    have hbase := sum_toQuadraticCoeffs_influence_sq_le_rpow
      δ hδ hn f F hf hF
    calc
      (∑ i, q.influence i ^ 2) =
          ∑ i, (toQuadraticCoeffs 0 f F).influence i ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rfl
      _ ≤ 25 * scale n (3 + 12 * δ) := hbase
  have ht4 : 0 ≤ τ ^ 4 := by positivity
  have habspow : |τ| ^ 4 = τ ^ 4 := by
    rw [← abs_pow, abs_of_nonneg ht4]
  calc
    |uniformExpectation (fun S : Finset (Fin n) ↦
        Real.cos (τ * sliceQuadratic f₀ f F S)) -
      gaussianExpectation (fun x ↦
        Real.cos (τ * (toQuadraticCoeffs f₀ f F).eval x))| ≤
        (27 / 4 : ℝ) * 1 * (τ ^ 4 * ∑ i, q.influence i ^ 2) := hinv
    _ ≤ (27 / 4 : ℝ) * τ ^ 4 *
        (25 * scale n (3 + 12 * δ)) := by
      have hm := mul_le_mul_of_nonneg_left hsum
        (mul_nonneg (show (0 : ℝ) ≤ 27 / 4 by norm_num) ht4)
      simpa only [mul_one, mul_assoc] using hm
    _ = (675 / 4 : ℝ) * |τ| ^ 4 * scale n (3 + 12 * δ) := by
      rw [habspow]
      ring

lemma sin_slice_to_multilinearGaussian_le
    (δ : ℝ) (hδ : 0 ≤ δ) (hn : 1 ≤ n)
    (f₀ : ℝ) (f : Fin n → ℝ) (F : Fin n → Fin n → ℝ)
    (hf : ∀ i, |f i| ≤ scale n (1 / 2 + 3 * δ))
    (hF : ∀ i j, |F i j| ≤ 1) (τ : ℝ) :
    |uniformExpectation (fun S : Finset (Fin n) ↦
        Real.sin (τ * sliceQuadratic f₀ f F S)) -
      gaussianExpectation (fun x ↦
        Real.sin (τ * (toQuadraticCoeffs f₀ f F).eval x))| ≤
      (675 / 4 : ℝ) * |τ| ^ 4 * scale n (3 + 12 * δ) := by
  let q := toQuadraticCoeffs f₀ f F
  let qs := scaleQuadraticCoeffs τ q
  have hinv := quadratic_invariance qs isBoundedC4Test_sin
  have hrademacher : rademacherExpectation (fun x ↦ Real.sin (qs.eval x)) =
      uniformExpectation (fun S : Finset (Fin n) ↦
        Real.sin (τ * sliceQuadratic f₀ f F S)) := by
    rw [rademacherExpectation_eq_uniformFinset]
    apply uniformExpectation_congr
    intro S
    dsimp only [qs]
    rw [scaleQuadraticCoeffs_eval, toQuadraticCoeffs_eval_signOfSet]
  have hgaussian : gaussianExpectation (fun x ↦ Real.sin (qs.eval x)) =
      gaussianExpectation (fun x ↦
        Real.sin (τ * (toQuadraticCoeffs f₀ f F).eval x)) := by
    apply congrArg gaussianExpectation
    funext x
    dsimp only [qs, q]
    rw [scaleQuadraticCoeffs_eval]
  rw [hrademacher, hgaussian,
    scaleQuadraticCoeffs_sum_influence_sq] at hinv
  have hsum : (∑ i, q.influence i ^ 2) ≤
      25 * scale n (3 + 12 * δ) := by
    have hbase := sum_toQuadraticCoeffs_influence_sq_le_rpow
      δ hδ hn f F hf hF
    calc
      (∑ i, q.influence i ^ 2) =
          ∑ i, (toQuadraticCoeffs 0 f F).influence i ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rfl
      _ ≤ 25 * scale n (3 + 12 * δ) := hbase
  have ht4 : 0 ≤ τ ^ 4 := by positivity
  have habspow : |τ| ^ 4 = τ ^ 4 := by
    rw [← abs_pow, abs_of_nonneg ht4]
  calc
    |uniformExpectation (fun S : Finset (Fin n) ↦
        Real.sin (τ * sliceQuadratic f₀ f F S)) -
      gaussianExpectation (fun x ↦
        Real.sin (τ * (toQuadraticCoeffs f₀ f F).eval x))| ≤
        (27 / 4 : ℝ) * 1 * (τ ^ 4 * ∑ i, q.influence i ^ 2) := hinv
    _ ≤ (27 / 4 : ℝ) * τ ^ 4 *
        (25 * scale n (3 + 12 * δ)) := by
      have hm := mul_le_mul_of_nonneg_left hsum
        (mul_nonneg (show (0 : ℝ) ≤ 27 / 4 by norm_num) ht4)
      simpa only [mul_one, mul_assoc] using hm
    _ = (675 / 4 : ℝ) * |τ| ^ 4 * scale n (3 + 12 * δ) := by
      rw [habspow]
      ring

lemma cos_multilinearGaussian_to_full_le
    (f₀ : ℝ) (f : Fin n → ℝ) (F : Fin n → Fin n → ℝ) (τ : ℝ) :
    |gaussianExpectation (fun x ↦
        Real.cos (τ * (toQuadraticCoeffs f₀ f F).eval x)) -
      gaussianExpectation (fun x ↦
        Real.cos (τ * quadraticPolynomial f₀ f F x))| ≤
      |τ| * √(2 * ∑ i, F i i ^ 2) := by
  let U : (Fin n → ℝ) → ℝ := fun x ↦
    τ * (toQuadraticCoeffs f₀ f F).eval x
  let V : (Fin n → ℝ) → ℝ := fun x ↦
    τ * quadraticPolynomial f₀ f F x
  have hDint := (gaussianDiagonalCorrection_memLp_two F).integrable (by norm_num)
  have hUmeas : AEStronglyMeasurable U (gaussianProductMeasure n) := by
    dsimp only [U]
    exact (measurable_const.mul (toQuadraticCoeffs f₀ f F).measurable_eval).aestronglyMeasurable
  have hVmeas : AEStronglyMeasurable V (gaussianProductMeasure n) := by
    have hfull : (fun x ↦ quadraticPolynomial f₀ f F x) =
        fun x ↦ (toQuadraticCoeffs f₀ f F).eval x + gaussianDiagonalCorrection F x := by
      funext x
      exact quadraticPolynomial_eq_multilinear_add_diagonal f₀ f F x
    rw [show V = fun x ↦ τ *
        ((toQuadraticCoeffs f₀ f F).eval x + gaussianDiagonalCorrection F x) by
      funext x
      dsimp only [V]
      rw [quadraticPolynomial_eq_multilinear_add_diagonal]]
    exact (measurable_const.aestronglyMeasurable.mul
      ((toQuadraticCoeffs f₀ f F).measurable_eval.aestronglyMeasurable.add
        (gaussianDiagonalCorrection_memLp_two F).aestronglyMeasurable))
  have hcosU : Integrable (fun x ↦ Real.cos (U x)) (gaussianProductMeasure n) := by
    apply Integrable.of_bound (Real.continuous_cos.comp_aestronglyMeasurable hUmeas) 1
    exact Filter.Eventually.of_forall fun x ↦ by
      simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (U x)
  have hcosV : Integrable (fun x ↦ Real.cos (V x)) (gaussianProductMeasure n) := by
    apply Integrable.of_bound (Real.continuous_cos.comp_aestronglyMeasurable hVmeas) 1
    exact Filter.Eventually.of_forall fun x ↦ by
      simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (V x)
  have hmajor : Integrable (fun x ↦ |τ| * |gaussianDiagonalCorrection F x|)
      (gaussianProductMeasure n) := by
    simpa only [Real.norm_eq_abs] using hDint.norm.const_mul |τ|
  have hdiffAbs : Integrable (fun x ↦ |Real.cos (U x) - Real.cos (V x)|)
      (gaussianProductMeasure n) := by
    convert (hcosU.sub hcosV).norm using 1 <;> rfl
  unfold gaussianExpectation
  rw [← integral_sub hcosU hcosV]
  calc
    |∫ x, Real.cos (U x) - Real.cos (V x) ∂gaussianProductMeasure n| ≤
        ∫ x, |Real.cos (U x) - Real.cos (V x)|
          ∂gaussianProductMeasure n := abs_integral_le_integral_abs
    _ ≤ ∫ x, |τ| * |gaussianDiagonalCorrection F x|
          ∂gaussianProductMeasure n := by
      apply integral_mono hdiffAbs hmajor
      intro x
      calc
        |Real.cos (U x) - Real.cos (V x)| ≤ |U x - V x| :=
          Real.abs_cos_sub_cos_le _ _
        _ = |τ| * |gaussianDiagonalCorrection F x| := by
          dsimp only [U, V]
          rw [quadraticPolynomial_eq_multilinear_add_diagonal]
          rw [← mul_sub, abs_mul]
          congr 1
          rw [show (toQuadraticCoeffs f₀ f F).eval x -
              ((toQuadraticCoeffs f₀ f F).eval x +
                gaussianDiagonalCorrection F x) =
              -gaussianDiagonalCorrection F x by ring,
            abs_neg]
    _ = |τ| * ∫ x, |gaussianDiagonalCorrection F x|
          ∂gaussianProductMeasure n := by rw [integral_const_mul]
    _ ≤ |τ| * √(2 * ∑ i, F i i ^ 2) := by
      gcongr
      exact integral_abs_gaussianDiagonalCorrection_le F

lemma sin_multilinearGaussian_to_full_le
    (f₀ : ℝ) (f : Fin n → ℝ) (F : Fin n → Fin n → ℝ) (τ : ℝ) :
    |gaussianExpectation (fun x ↦
        Real.sin (τ * (toQuadraticCoeffs f₀ f F).eval x)) -
      gaussianExpectation (fun x ↦
        Real.sin (τ * quadraticPolynomial f₀ f F x))| ≤
      |τ| * √(2 * ∑ i, F i i ^ 2) := by
  let U : (Fin n → ℝ) → ℝ := fun x ↦
    τ * (toQuadraticCoeffs f₀ f F).eval x
  let V : (Fin n → ℝ) → ℝ := fun x ↦
    τ * quadraticPolynomial f₀ f F x
  have hDint := (gaussianDiagonalCorrection_memLp_two F).integrable (by norm_num)
  have hUmeas : AEStronglyMeasurable U (gaussianProductMeasure n) := by
    dsimp only [U]
    exact (measurable_const.mul (toQuadraticCoeffs f₀ f F).measurable_eval).aestronglyMeasurable
  have hVmeas : AEStronglyMeasurable V (gaussianProductMeasure n) := by
    have hfull : (fun x ↦ quadraticPolynomial f₀ f F x) =
        fun x ↦ (toQuadraticCoeffs f₀ f F).eval x + gaussianDiagonalCorrection F x := by
      funext x
      exact quadraticPolynomial_eq_multilinear_add_diagonal f₀ f F x
    rw [show V = fun x ↦ τ *
        ((toQuadraticCoeffs f₀ f F).eval x + gaussianDiagonalCorrection F x) by
      funext x
      dsimp only [V]
      rw [quadraticPolynomial_eq_multilinear_add_diagonal]]
    exact (measurable_const.aestronglyMeasurable.mul
      ((toQuadraticCoeffs f₀ f F).measurable_eval.aestronglyMeasurable.add
        (gaussianDiagonalCorrection_memLp_two F).aestronglyMeasurable))
  have hsinU : Integrable (fun x ↦ Real.sin (U x)) (gaussianProductMeasure n) := by
    apply Integrable.of_bound (Real.continuous_sin.comp_aestronglyMeasurable hUmeas) 1
    exact Filter.Eventually.of_forall fun x ↦ by
      simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (U x)
  have hsinV : Integrable (fun x ↦ Real.sin (V x)) (gaussianProductMeasure n) := by
    apply Integrable.of_bound (Real.continuous_sin.comp_aestronglyMeasurable hVmeas) 1
    exact Filter.Eventually.of_forall fun x ↦ by
      simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (V x)
  have hmajor : Integrable (fun x ↦ |τ| * |gaussianDiagonalCorrection F x|)
      (gaussianProductMeasure n) := by
    simpa only [Real.norm_eq_abs] using hDint.norm.const_mul |τ|
  have hdiffAbs : Integrable (fun x ↦ |Real.sin (U x) - Real.sin (V x)|)
      (gaussianProductMeasure n) := by
    convert (hsinU.sub hsinV).norm using 1 <;> rfl
  unfold gaussianExpectation
  rw [← integral_sub hsinU hsinV]
  calc
    |∫ x, Real.sin (U x) - Real.sin (V x) ∂gaussianProductMeasure n| ≤
        ∫ x, |Real.sin (U x) - Real.sin (V x)|
          ∂gaussianProductMeasure n := abs_integral_le_integral_abs
    _ ≤ ∫ x, |τ| * |gaussianDiagonalCorrection F x|
          ∂gaussianProductMeasure n := by
      apply integral_mono hdiffAbs hmajor
      intro x
      calc
        |Real.sin (U x) - Real.sin (V x)| ≤ |U x - V x| :=
          Real.abs_sin_sub_sin_le _ _
        _ = |τ| * |gaussianDiagonalCorrection F x| := by
          dsimp only [U, V]
          rw [quadraticPolynomial_eq_multilinear_add_diagonal]
          rw [← mul_sub, abs_mul]
          congr 1
          rw [show (toQuadraticCoeffs f₀ f F).eval x -
              ((toQuadraticCoeffs f₀ f F).eval x +
                gaussianDiagonalCorrection F x) =
              -gaussianDiagonalCorrection F x by ring,
            abs_neg]
    _ = |τ| * ∫ x, |gaussianDiagonalCorrection F x|
          ∂gaussianProductMeasure n := by rw [integral_const_mul]
    _ ≤ |τ| * √(2 * ∑ i, F i i ^ 2) := by
      gcongr
      exact integral_abs_gaussianDiagonalCorrection_le F

/-- KSSS Lemma 11.6 in characteristic-function form, including the
`L²`-sharp correction from the multilinear Gaussian polynomial to the full
Gaussian quadratic. -/
lemma norm_sliceCharacteristic_sub_gaussianQuadratic_le
    (δ : ℝ) (hδ : 0 ≤ δ) (hn : 1 ≤ n)
    (f₀ : ℝ) (f : Fin n → ℝ) (F : Fin n → Fin n → ℝ)
    (hf : ∀ i, |f i| ≤ scale n (1 / 2 + 3 * δ))
    (hF : ∀ i j, |F i j| ≤ 1) (τ : ℝ) :
    ‖finiteCharacteristic (sliceQuadratic f₀ f F) τ -
        gaussianQuadraticCharacteristic f₀ f F τ‖ ≤
      2 * ((675 / 4 : ℝ) * |τ| ^ 4 * scale n (3 + 12 * δ) +
        |τ| * √(2 * ∑ i, F i i ^ 2)) := by
  let A : ℝ := (675 / 4 : ℝ) * |τ| ^ 4 * scale n (3 + 12 * δ)
  let B : ℝ := |τ| * √(2 * ∑ i, F i i ^ 2)
  let Rc : ℝ := uniformExpectation (fun S : Finset (Fin n) ↦
    Real.cos (τ * sliceQuadratic f₀ f F S))
  let Rs : ℝ := uniformExpectation (fun S : Finset (Fin n) ↦
    Real.sin (τ * sliceQuadratic f₀ f F S))
  let Mc : ℝ := gaussianExpectation (fun x ↦
    Real.cos (τ * (toQuadraticCoeffs f₀ f F).eval x))
  let Ms : ℝ := gaussianExpectation (fun x ↦
    Real.sin (τ * (toQuadraticCoeffs f₀ f F).eval x))
  let Gc : ℝ := gaussianExpectation (fun x ↦
    Real.cos (τ * quadraticPolynomial f₀ f F x))
  let Gs : ℝ := gaussianExpectation (fun x ↦
    Real.sin (τ * quadraticPolynomial f₀ f F x))
  have hRc : |Rc - Mc| ≤ A := by
    exact cos_slice_to_multilinearGaussian_le δ hδ hn f₀ f F hf hF τ
  have hRs : |Rs - Ms| ≤ A := by
    exact sin_slice_to_multilinearGaussian_le δ hδ hn f₀ f F hf hF τ
  have hMc : |Mc - Gc| ≤ B := by
    exact cos_multilinearGaussian_to_full_le f₀ f F τ
  have hMs : |Ms - Gs| ≤ B := by
    exact sin_multilinearGaussian_to_full_le f₀ f F τ
  have hcos : |Rc - Gc| ≤ A + B := by
    calc
      |Rc - Gc| = |(Rc - Mc) + (Mc - Gc)| := by ring_nf
      _ ≤ |Rc - Mc| + |Mc - Gc| := abs_add_le _ _
      _ ≤ A + B := add_le_add hRc hMc
  have hsin : |Rs - Gs| ≤ A + B := by
    calc
      |Rs - Gs| = |(Rs - Ms) + (Ms - Gs)| := by ring_nf
      _ ≤ |Rs - Ms| + |Ms - Gs| := abs_add_le _ _
      _ ≤ A + B := add_le_add hRs hMs
  rw [finiteCharacteristic_eq_cos_sin]
  unfold gaussianQuadraticCharacteristic
  change ‖((Rc : ℂ) + (Rs : ℂ) * Complex.I) -
      ((Gc : ℂ) + (Gs : ℂ) * Complex.I)‖ ≤ 2 * (A + B)
  rw [show ((Rc : ℂ) + (Rs : ℂ) * Complex.I) -
      ((Gc : ℂ) + (Gs : ℂ) * Complex.I) =
      ((Rc - Gc : ℝ) : ℂ) + ((Rs - Gs : ℝ) : ℂ) * Complex.I by
    push_cast
    ring]
  calc
    ‖((Rc - Gc : ℝ) : ℂ) + ((Rs - Gs : ℝ) : ℂ) * Complex.I‖ ≤
        ‖((Rc - Gc : ℝ) : ℂ)‖ +
          ‖((Rs - Gs : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = |Rc - Gc| + |Rs - Gs| := by
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_I,
        mul_one, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ 2 * (A + B) := by linarith

lemma diagonalCorrection_sqrt_le_two_sqrt_nat
    (F : Fin n → Fin n → ℝ) (hF : ∀ i j, |F i j| ≤ 1) :
    √(2 * ∑ i, F i i ^ 2) ≤ 2 * √(n : ℝ) := by
  have hdiag : (∑ i, F i i ^ 2) ≤ (n : ℝ) := by
    calc
      (∑ i, F i i ^ 2) ≤ ∑ _i : Fin n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        simpa only [sq_abs, one_pow] using
          (sq_le_sq₀ (abs_nonneg (F i i)) (by norm_num)).2 (hF i i)
      _ = (n : ℝ) := by simp
  have hsqrt : √(2 * ∑ i, F i i ^ 2) ≤ √(2 * (n : ℝ)) := by
    apply Real.sqrt_le_sqrt
    gcongr
  calc
    √(2 * ∑ i, F i i ^ 2) ≤ √(2 * (n : ℝ)) := hsqrt
    _ ≤ 2 * √(n : ℝ) := by
      rw [Real.sqrt_le_iff]
      constructor
      · positivity
      · rw [show (2 * √(n : ℝ)) ^ 2 = 4 * (√(n : ℝ)) ^ 2 by ring,
          Real.sq_sqrt (Nat.cast_nonneg n)]
        nlinarith [show (0 : ℝ) ≤ (n : ℝ) by positivity]

/-- Exponent-normalized characteristic estimate from KSSS Lemma 11.6. -/
lemma norm_sliceCharacteristic_sub_gaussianQuadratic_le_ksss
    (δ : ℝ) (hδ : 0 ≤ δ) (hn : 1 ≤ n)
    (f₀ : ℝ) (f : Fin n → ℝ) (F : Fin n → Fin n → ℝ)
    (hf : ∀ i, |f i| ≤ scale n (1 / 2 + 3 * δ))
    (hF : ∀ i j, |F i j| ≤ 1) (τ : ℝ) :
    ‖finiteCharacteristic (sliceQuadratic f₀ f F) τ -
        gaussianQuadraticCharacteristic f₀ f F τ‖ ≤
      (675 / 2 : ℝ) * |τ| ^ 4 * scale n (3 + 12 * δ) +
        4 * |τ| * scale n (1 / 2) := by
  have hbase := norm_sliceCharacteristic_sub_gaussianQuadratic_le
    δ hδ hn f₀ f F hf hF τ
  have hsqrt := diagonalCorrection_sqrt_le_two_sqrt_nat F hF
  have hsqrtScale : √(n : ℝ) = scale n (1 / 2) := by
    rw [Real.sqrt_eq_rpow]
    rfl
  calc
    ‖finiteCharacteristic (sliceQuadratic f₀ f F) τ -
        gaussianQuadraticCharacteristic f₀ f F τ‖ ≤
      2 * ((675 / 4 : ℝ) * |τ| ^ 4 * scale n (3 + 12 * δ) +
        |τ| * √(2 * ∑ i, F i i ^ 2)) := hbase
    _ ≤ (675 / 2 : ℝ) * |τ| ^ 4 * scale n (3 + 12 * δ) +
        4 * |τ| * scale n (1 / 2) := by
      rw [← hsqrtScale]
      nlinarith [mul_le_mul_of_nonneg_left hsqrt (abs_nonneg τ)]

end GaussianDiagonalCorrection

section KSSSLemma111

variable {n m : ℕ}

/-- Composition of the weighted slice coupling with the full Gaussian
comparison. -/
lemma norm_productSliceCharacteristic_sub_gaussianQuadratic_le_of_weightedCoupling
    (P : BucketPartition (Fin n) (Fin m)) (ell : Fin m → ℕ)
    [Nonempty (ProductSlicePoint P ell)]
    (f₀ : ℝ) (f : Fin n → ℝ) (F : Fin n → Fin n → ℝ)
    (δ r q : ℝ) (hδ : 0 ≤ δ) (hn : 1 ≤ n) (hr : 0 ≤ r)
    (hf : ∀ i, |f i| ≤ scale n (1 / 2 + 3 * δ))
    (hF : ∀ i j, |F i j| ≤ 1)
    (C : FiniteWeightedCoupling (ProductSlicePoint P ell) (Finset (Fin n)))
    (hclose : C.IsClose (productSliceQuadratic P ell f₀ f F)
      (sliceQuadratic f₀ f F) r q) (τ : ℝ) :
    ‖finiteCharacteristic (productSliceQuadratic P ell f₀ f F) τ -
        gaussianQuadraticCharacteristic f₀ f F τ‖ ≤
      |τ| * (r + ksssQuadraticDifferenceBound n δ * q) +
        ((675 / 2 : ℝ) * |τ| ^ 4 * scale n (3 + 12 * δ) +
          4 * |τ| * scale n (1 / 2)) := by
  have hD : ∀ x y,
      |productSliceQuadratic P ell f₀ f F x - sliceQuadratic f₀ f F y| ≤
        ksssQuadraticDifferenceBound n δ := by
    intro x y
    simpa only [productSliceQuadratic, ksssQuadraticDifferenceBound,
      mul_one] using
      (abs_sliceQuadratic_sub_le f₀ f F 1
        (scale n (1 / 2 + 3 * δ)) (by norm_num)
        (scale_nonneg n _) hf hF x.1 y)
  have hcouple := C.norm_characteristic_sub_le_of_isClose_range
    (productSliceQuadratic P ell f₀ f F) (sliceQuadratic f₀ f F)
      r q (ksssQuadraticDifferenceBound n δ) τ hr
      (ksssQuadraticDifferenceBound_nonneg n δ) hclose hD
  have hgauss := norm_sliceCharacteristic_sub_gaussianQuadratic_le_ksss
    δ hδ hn f₀ f F hf hF τ
  calc
    ‖finiteCharacteristic (productSliceQuadratic P ell f₀ f F) τ -
        gaussianQuadraticCharacteristic f₀ f F τ‖ ≤
      ‖finiteCharacteristic (productSliceQuadratic P ell f₀ f F) τ -
          finiteCharacteristic (sliceQuadratic f₀ f F) τ‖ +
        ‖finiteCharacteristic (sliceQuadratic f₀ f F) τ -
          gaussianQuadraticCharacteristic f₀ f F τ‖ := by
      rw [show finiteCharacteristic (productSliceQuadratic P ell f₀ f F) τ -
          gaussianQuadraticCharacteristic f₀ f F τ =
          (finiteCharacteristic (productSliceQuadratic P ell f₀ f F) τ -
            finiteCharacteristic (sliceQuadratic f₀ f F) τ) +
          (finiteCharacteristic (sliceQuadratic f₀ f F) τ -
            gaussianQuadraticCharacteristic f₀ f F τ) by ring]
      exact norm_add_le _ _
    _ ≤ |τ| * (r + ksssQuadraticDifferenceBound n δ * q) +
        ((675 / 2 : ℝ) * |τ| ^ 4 * scale n (3 + 12 * δ) +
          4 * |τ| * scale n (1 / 2)) := add_le_add hcouple hgauss

/-- Source-exponent form of the characteristic-function conclusion of
Lemma 11.1. -/
lemma norm_productSliceCharacteristic_sub_gaussianQuadratic_le_ksss
    (P : BucketPartition (Fin n) (Fin m)) (ell : Fin m → ℕ)
    [Nonempty (ProductSlicePoint P ell)]
    (f₀ : ℝ) (f : Fin n → ℝ) (F : Fin n → Fin n → ℝ)
    (δ q : ℝ) (hδ : 0 ≤ δ) (hn : 1 ≤ n)
    (hf : ∀ i, |f i| ≤ scale n (1 / 2 + 3 * δ))
    (hF : ∀ i j, |F i j| ≤ 1)
    (C : FiniteWeightedCoupling (ProductSlicePoint P ell) (Finset (Fin n)))
    (hclose : C.IsClose (productSliceQuadratic P ell f₀ f F)
      (sliceQuadratic f₀ f F) (scale n (3 / 4 + 4 * δ)) q)
    (hexception : ksssQuadraticDifferenceBound n δ * q ≤
      scale n (3 / 4 + 4 * δ)) (τ : ℝ) :
    ‖finiteCharacteristic (productSliceQuadratic P ell f₀ f F) τ -
        gaussianQuadraticCharacteristic f₀ f F τ‖ ≤
      (675 / 2 : ℝ) * |τ| ^ 4 * scale n (3 + 12 * δ) +
        6 * |τ| * scale n (3 / 4 + 4 * δ) := by
  let r : ℝ := scale n (3 / 4 + 4 * δ)
  have hr0 : 0 ≤ r := scale_nonneg _ _
  have hbase :=
    norm_productSliceCharacteristic_sub_gaussianQuadratic_le_of_weightedCoupling
      P ell f₀ f F δ r q hδ hn hr0 hf hF C hclose τ
  have hhalf : scale n (1 / 2) ≤ r := by
    dsimp only [r]
    exact scale_mono_exponent hn (by linarith)
  change ‖finiteCharacteristic (productSliceQuadratic P ell f₀ f F) τ -
        gaussianQuadraticCharacteristic f₀ f F τ‖ ≤ _
  calc
    ‖finiteCharacteristic (productSliceQuadratic P ell f₀ f F) τ -
        gaussianQuadraticCharacteristic f₀ f F τ‖ ≤
      |τ| * (r + ksssQuadraticDifferenceBound n δ * q) +
        ((675 / 2 : ℝ) * |τ| ^ 4 * scale n (3 + 12 * δ) +
          4 * |τ| * scale n (1 / 2)) := hbase
    _ ≤ (675 / 2 : ℝ) * |τ| ^ 4 * scale n (3 + 12 * δ) +
        6 * |τ| * r := by
      have hτexc := mul_le_mul_of_nonneg_left hexception (abs_nonneg τ)
      have hτhalf := mul_le_mul_of_nonneg_left hhalf (abs_nonneg τ)
      nlinarith

/-- Exact eventual statement of KSSS Lemma 11.1, with explicit absolute
constants replacing the paper's `O` and `≲` notation. -/
def KSSSLemma111 : Prop :=
  ∀ d : ℝ, 0 < d → d < 1 / 4 →
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (m : ℕ) (P : BucketPartition (Fin n) (Fin m))
        (ell : Fin m → ℕ) (f₀ : ℝ) (f : Fin n → ℝ)
        (F : Fin n → Fin n → ℝ),
        IsKSSSPartition d P → IsNearBalanced d P ell →
        HasKSSSBalancedCoefficients d P f F →
        ∃ hleft : Nonempty (ProductSlicePoint P ell),
          letI := hleft
          |uniformExpectation (productSliceQuadratic P ell f₀ f F) -
              (f₀ + trace F)| ≤ 2 * scale n (3 / 4 + 4 * d) ∧
          |uniformVariance (productSliceQuadratic P ell f₀ f F) -
              (2 * frobeniusSq F + vectorSqNorm f)| ≤
            10 * scale n (7 / 4 + 7 * d) ∧
          ∀ τ : ℝ,
            ‖finiteCharacteristic (productSliceQuadratic P ell f₀ f F) τ -
                gaussianQuadraticCharacteristic f₀ f F τ‖ ≤
              (675 / 2 : ℝ) * |τ| ^ 4 * scale n (3 + 12 * d) +
                6 * |τ| * scale n (3 / 4 + 4 * d)

theorem ksssLemma111 : KSSSLemma111 := by
  intro d hd hd4
  have h113 := ksssLemma113 d hd hd4
  have hD := eventually_ksssQuadraticDifferenceBound_le_exp_log_sq d hd4
  filter_upwards [h113, hD, Filter.eventually_ge_atTop 1] with n hn113 hD hn
  intro m P ell f₀ f F hpart hell hcoeff
  have hcoupling := hn113 m P ell f₀ f F hpart hell hcoeff
  unfold HasQuadraticRademacherWeightedCoupling at hcoupling
  rcases hcoupling with ⟨hleft, C, hC⟩
  refine ⟨hleft, ?_⟩
  let := hleft
  have hδ0 : 0 ≤ d := hd.le
  have hq0 : 0 ≤ Real.exp (-(Real.log n) ^ 2 / 8) := Real.exp_nonneg _
  have hlinear := ksss_exception_linear_le d hd hn hD
  have hsquare := ksss_exception_sq_le d hd hn hD
  have hmean := productSlice_mean_error_ksss_of_weightedCoupling
    P ell f₀ f F d (Real.exp (-(Real.log n) ^ 2 / 8))
      hcoeff.2.1 hcoeff.2.2.1 C hC hlinear
  have hvariance := productSlice_variance_error_ksss_of_weightedCoupling
    P ell f₀ f F d (Real.exp (-(Real.log n) ^ 2 / 8))
      hδ0 hd4 hn hq0 hcoeff.1 hcoeff.2.1 hcoeff.2.2.1 C hC hsquare
  refine ⟨hmean, hvariance, ?_⟩
  intro τ
  exact norm_productSliceCharacteristic_sub_gaussianQuadratic_le_ksss
    P ell f₀ f F d (Real.exp (-(Real.log n) ^ 2 / 8))
      hδ0 hn hcoeff.2.1 hcoeff.2.2.1 C hC hlinear τ

end KSSSLemma111

end Erdos88.BooleanSlices
