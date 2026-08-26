/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPolynomial

/-!
# Finite prime-local coefficient choices

A prime can divide the left coefficient, the right coefficient, or both.
Within each affine family it occupies at most one coordinate. A simultaneous
first/companion choice is permitted only on a collision edge. In the
arithmetic application the edge set is empty when the companion slope is
not invertible.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

def primePairStateWeight (X Y : ℂ) (r : Fin 3) : ℂ :=
  if r = 0 then -X else if r = 1 then -Y else X * Y

abbrev primePairStateLeft (r : Fin 3) : Prop := r ≠ 1

abbrev primePairStateRight (r : Fin 3) : Prop := r ≠ 0

theorem primePairStateWeight_eq_signed_powers (X Y : ℂ) (r : Fin 3) :
    primePairStateWeight X Y r =
      (if primePairStateLeft r then -X else 1) *
        (if primePairStateRight r then -Y else 1) := by
  fin_cases r <;> simp [primePairStateWeight, primePairStateLeft, primePairStateRight]

theorem primePairState_nonempty (r : Fin 3) :
    primePairStateLeft r ∨ primePairStateRight r := by
  fin_cases r <;> simp [primePairStateLeft, primePairStateRight]

theorem sum_primePairStateWeight (X Y : ℂ) :
    (∑ r : Fin 3, primePairStateWeight X Y r) = selbergPairPolynomial X Y := by
  rw [Fin.sum_univ_three]
  simp [primePairStateWeight, selbergPairPolynomial]
  ring

theorem sum_primePairStateWeight_mul (X X' Y Y' : ℂ) :
    (∑ a : Fin 3, ∑ b : Fin 3,
      primePairStateWeight X X' a * primePairStateWeight Y Y' b) =
      selbergPairPolynomial X X' * selbergPairPolynomial Y Y' := by
  simp_rw [← Finset.mul_sum, sum_primePairStateWeight, ← Finset.sum_mul]
  rw [sum_primePairStateWeight]

theorem norm_primePairStateWeight_le {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    {X Y : ℂ} (hX : ‖X‖ ≤ ρ) (hY : ‖Y‖ ≤ ρ) (r : Fin 3) :
    ‖primePairStateWeight X Y r‖ ≤ ρ := by
  fin_cases r
  · simpa [primePairStateWeight] using hX
  · simpa [primePairStateWeight] using hY
  · simp only [primePairStateWeight]
    norm_num
    have hmul := mul_le_mul hX hY (norm_nonneg _) hρ0
    nlinarith

abbrev NonemptyDoubledPrimeChoice (ι : Type*) :=
  (ι × Fin 3) ⊕ ((ι × Fin 3) ⊕ ((ι × ι) × (Fin 3 × Fin 3)))

abbrev DoubledPrimeChoice (ι : Type*) := Option (NonemptyDoubledPrimeChoice ι)

theorem card_nonemptyDoubledPrimeChoice (ι : Type*) [Fintype ι] :
    Fintype.card (NonemptyDoubledPrimeChoice ι) =
      6 * Fintype.card ι + 9 * (Fintype.card ι) ^ 2 := by
  simp only [NonemptyDoubledPrimeChoice, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_fin]
  ring

def doubledPrimeChoiceWeight {ι : Type*} [DecidableEq ι]
    (edges : Finset (ι × ι)) (companion : Bool) (p : ℝ)
    (X X' Y Y' : ι → ℂ) : DoubledPrimeChoice ι → ℂ
  | none => 1
  | some (.inl (i, a)) => primePairStateWeight (X i) (X' i) a / p
  | some (.inr (.inl (j, b))) =>
      if companion then primePairStateWeight (Y j) (Y' j) b / p else 0
  | some (.inr (.inr (ij, a, b))) =>
      if ij ∈ edges then
        primePairStateWeight (X ij.1) (X' ij.1) a *
          primePairStateWeight (Y ij.2) (Y' ij.2) b / p
      else 0

theorem norm_doubledPrimeChoiceWeight_some_le
    {ι : Type*} [DecidableEq ι] (edges : Finset (ι × ι)) (companion : Bool)
    {p ρ : ℝ} (hp : 0 < p) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (X X' Y Y' : ι → ℂ)
    (hX : ∀ i, ‖X i‖ ≤ ρ) (hX' : ∀ i, ‖X' i‖ ≤ ρ)
    (hY : ∀ i, ‖Y i‖ ≤ ρ) (hY' : ∀ i, ‖Y' i‖ ≤ ρ)
    (c : NonemptyDoubledPrimeChoice ι) :
    ‖doubledPrimeChoiceWeight edges companion p X X' Y Y' (some c)‖ ≤ ρ / p := by
  have hfirst (i : ι) (r : Fin 3) := norm_primePairStateWeight_le hρ0 hρ1 (hX i) (hX' i) r
  have hsecond (i : ι) (r : Fin 3) := norm_primePairStateWeight_le hρ0 hρ1 (hY i) (hY' i) r
  rcases c with ⟨i, a⟩ | c
  · simp only [doubledPrimeChoiceWeight, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hp]
    exact div_le_div_of_nonneg_right (hfirst i a) hp.le
  rcases c with ⟨j, b⟩ | ⟨ij, a, b⟩
  · cases companion
    · simp [doubledPrimeChoiceWeight, div_nonneg hρ0 hp.le]
    · simp only [doubledPrimeChoiceWeight, ↓reduceIte, norm_div,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
      exact div_le_div_of_nonneg_right (hsecond j b) hp.le
  · by_cases hij : ij ∈ edges
    · simp only [doubledPrimeChoiceWeight, if_pos hij, norm_div, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
      apply div_le_div_of_nonneg_right _ hp.le
      have hmul := mul_le_mul (hfirst ij.1 a) (hsecond ij.2 b) (norm_nonneg _) hρ0
      nlinarith
    · simp [doubledPrimeChoiceWeight, hij, div_nonneg hρ0 hp.le]

theorem sum_norm_doubledPrimeChoiceWeight_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (edges : Finset (ι × ι)) (companion : Bool)
    {p ρ : ℝ} (hp : 0 < p) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (X X' Y Y' : ι → ℂ)
    (hX : ∀ i, ‖X i‖ ≤ ρ) (hX' : ∀ i, ‖X' i‖ ≤ ρ)
    (hY : ∀ i, ‖Y i‖ ≤ ρ) (hY' : ∀ i, ‖Y' i‖ ≤ ρ) :
    (∑ c : DoubledPrimeChoice ι, ‖doubledPrimeChoiceWeight edges companion p X X' Y Y' c‖) ≤
      1 + (Fintype.card (NonemptyDoubledPrimeChoice ι) : ℝ) * ρ / p := by
  rw [Fintype.sum_option]
  simp only [doubledPrimeChoiceWeight, norm_one]
  calc
    _ ≤ 1 + ∑ _c : NonemptyDoubledPrimeChoice ι, ρ / p := by
      apply add_le_add le_rfl
      exact Finset.sum_le_sum fun c hc ↦
        norm_doubledPrimeChoiceWeight_some_le edges companion hp hρ0 hρ1
          X X' Y Y' hX hX' hY hY' c
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

theorem sum_doubledPrimeChoiceWeight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (edges : Finset (ι × ι)) (companion : Bool) (p : ℝ) (X X' Y Y' : ι → ℂ) :
    (∑ c : DoubledPrimeChoice ι, doubledPrimeChoiceWeight edges companion p X X' Y Y' c) =
      doubledFourierLocalPolynomial Finset.univ edges companion p
        (fun i ↦ selbergPairPolynomial (X i) (X' i))
        (fun i ↦ selbergPairPolynomial (Y i) (Y' i)) := by
  classical
  simp only [Fintype.sum_option, Fintype.sum_sum_type, Fintype.sum_prod_type,
    doubledPrimeChoiceWeight]
  simp_rw [Finset.sum_ite_irrel, ← Finset.sum_div, ← Finset.mul_sum,
    sum_primePairStateWeight, ← Finset.sum_mul]
  simp_rw [sum_primePairStateWeight]
  simp only [Finset.sum_const_zero]
  have hedgeSum (f : ι × ι → ℂ) :
      (∑ i : ι, ∑ j : ι, if (i, j) ∈ edges then f (i, j) else 0) =
        ∑ ij ∈ edges, f ij := by
    rw [← Fintype.sum_prod_type (fun ij : ι × ι ↦ if ij ∈ edges then f ij else 0)]
    simp
  rw [hedgeSum (fun ij ↦ selbergPairPolynomial (X ij.1) (X' ij.1) *
    selbergPairPolynomial (Y ij.2) (Y' ij.2) / (p : ℂ))]
  rw [← Finset.sum_div]
  unfold doubledFourierLocalPolynomial
  cases companion <;> simp <;> ring

theorem norm_doubledFourierLocalPolynomial_sub_one_le
    {ι : Type*} [Fintype ι]
    (edges : Finset (ι × ι)) (companion : Bool)
    {p ρ : ℝ} (hp : 0 < p) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (X X' Y Y' : ι → ℂ)
    (hX : ∀ i, ‖X i‖ ≤ ρ) (hX' : ∀ i, ‖X' i‖ ≤ ρ)
    (hY : ∀ i, ‖Y i‖ ≤ ρ) (hY' : ∀ i, ‖Y' i‖ ≤ ρ) :
    ‖doubledFourierLocalPolynomial Finset.univ edges companion p
        (fun i ↦ selbergPairPolynomial (X i) (X' i))
        (fun i ↦ selbergPairPolynomial (Y i) (Y' i)) - 1‖ ≤
      (Fintype.card (NonemptyDoubledPrimeChoice ι) : ℝ) * ρ / p := by
  classical
  rw [← sum_doubledPrimeChoiceWeight, Fintype.sum_option]
  simp only [doubledPrimeChoiceWeight, add_sub_cancel_left]
  calc
    _ ≤ ∑ c : NonemptyDoubledPrimeChoice ι,
        ‖doubledPrimeChoiceWeight edges companion p X X' Y Y' (some c)‖ := norm_sum_le _ _
    _ ≤ ∑ _c : NonemptyDoubledPrimeChoice ι, ρ / p := Finset.sum_le_sum fun c hc ↦
      norm_doubledPrimeChoiceWeight_some_le edges companion hp hρ0 hρ1
        X X' Y Y' hX hX' hY hY' c
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- Transposing the finite prime-by-choice table gives the exact finite
Euler product.  The remaining arithmetic step is to identify each choice
function with its four squarefree divisor tuples. -/
theorem sum_prod_doubledPrimeChoiceWeight
    {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Finset ℕ)
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (X X' Y Y' : ℕ → ι → ℂ) :
    (∑ c : P → DoubledPrimeChoice ι, ∏ p : P,
      doubledPrimeChoiceWeight (edges p) (companion p) p (X p) (X' p) (Y p) (Y' p) (c p)) =
      ∏ p ∈ P, doubledFourierLocalPolynomial Finset.univ (edges p) (companion p) p
        (fun i ↦ selbergPairPolynomial (X p i) (X' p i))
        (fun i ↦ selbergPairPolynomial (Y p i) (Y' p i)) := by
  classical
  rw [← Fintype.prod_sum]
  simp_rw [sum_doubledPrimeChoiceWeight]
  exact Finset.prod_coe_sort P (fun p : ℕ ↦
    doubledFourierLocalPolynomial Finset.univ (edges p) (companion p) p
      (fun i ↦ selbergPairPolynomial (X p i) (X' p i))
      (fun i ↦ selbergPairPolynomial (Y p i) (Y' p i)))

theorem sum_norm_prod_doubledPrimeChoiceWeight_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Finset ℕ)
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (X X' Y Y' : ℕ → ι → ℂ) (ρ : ℕ → ℝ)
    (hp : ∀ p ∈ P, 0 < p) (hρ0 : ∀ p ∈ P, 0 ≤ ρ p) (hρ1 : ∀ p ∈ P, ρ p ≤ 1)
    (hX : ∀ p ∈ P, ∀ i, ‖X p i‖ ≤ ρ p) (hX' : ∀ p ∈ P, ∀ i, ‖X' p i‖ ≤ ρ p)
    (hY : ∀ p ∈ P, ∀ i, ‖Y p i‖ ≤ ρ p) (hY' : ∀ p ∈ P, ∀ i, ‖Y' p i‖ ≤ ρ p) :
    (∑ c : P → DoubledPrimeChoice ι, ‖∏ p : P,
      doubledPrimeChoiceWeight (edges p) (companion p) p (X p) (X' p) (Y p) (Y' p) (c p)‖) ≤
      ∏ p ∈ P, (1 + (Fintype.card (NonemptyDoubledPrimeChoice ι) : ℝ) * ρ p / p) := by
  classical
  simp_rw [norm_prod]
  rw [← Fintype.prod_sum (fun (p : P) (c : DoubledPrimeChoice ι) ↦
    ‖doubledPrimeChoiceWeight (edges p) (companion p) p
      (X p) (X' p) (Y p) (Y' p) c‖)]
  calc
    _ ≤ ∏ p : P, (1 + (Fintype.card (NonemptyDoubledPrimeChoice ι) : ℝ) * ρ p / p) := by
      apply Finset.prod_le_prod
      · intro p hmem
        exact Finset.sum_nonneg fun c hc ↦ norm_nonneg _
      · intro p hmem
        exact sum_norm_doubledPrimeChoiceWeight_le (edges p) (companion p)
          (by exact_mod_cast hp p p.property) (hρ0 p p.property) (hρ1 p p.property)
          (X p) (X' p) (Y p) (Y' p)
          (hX p p.property) (hX' p p.property) (hY p p.property) (hY' p p.property)
    _ = _ := Finset.prod_coe_sort P (fun p : ℕ ↦
      1 + (Fintype.card (NonemptyDoubledPrimeChoice ι) : ℝ) * ρ p / p)

end

end Erdos4b
