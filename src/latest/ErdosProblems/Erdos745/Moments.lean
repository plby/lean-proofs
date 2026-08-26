import ErdosProblems.Erdos745.Model

/-!
# Finite first and second moments in the exact graph law
-/

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Erdos745

noncomputable section

attribute [local instance] Classical.propDecidable

local instance (n : ℕ) : MeasurableSingletonClass (SimpleGraph (Fin n)) :=
  ⟨fun G ↦ measurableSet_graphEvent {G}⟩

/-- The probability of an individual labelled graph. -/
def atomWeight (lam : ℝ) (n : ℕ) (G : SimpleGraph (Fin n)) : ℝ :=
  (randomGraph lam n).real {G}

theorem atomWeight_nonneg (lam : ℝ) (n : ℕ) (G : SimpleGraph (Fin n)) :
    0 ≤ atomWeight lam n G := measureReal_nonneg

@[simp] theorem sum_atomWeight (lam : ℝ) (n : ℕ) :
    ∑ G : SimpleGraph (Fin n), atomWeight lam n G = 1 := by
  simp [atomWeight]

theorem probability_eq_sum (lam : ℝ) (n : ℕ)
    (P : SimpleGraph (Fin n) → Prop) :
    probability lam n P =
      ∑ G : SimpleGraph (Fin n), if P G then atomWeight lam n G else 0 := by
  classical
  rw [← Finset.sum_filter]
  simp [probability, atomWeight]

/-- Expectation as a finite sum of atom weights. -/
def expectation (lam : ℝ) (n : ℕ) (X : SimpleGraph (Fin n) → ℝ) : ℝ :=
  ∑ G, atomWeight lam n G * X G

@[simp] theorem expectation_const (lam : ℝ) (n : ℕ) (a : ℝ) :
    expectation lam n (fun _ ↦ a) = a := by
  simp [expectation, ← Finset.sum_mul]

theorem expectation_nonneg {lam : ℝ} {n : ℕ}
    {X : SimpleGraph (Fin n) → ℝ} (hX : ∀ G, 0 ≤ X G) :
    0 ≤ expectation lam n X := by
  exact Finset.sum_nonneg fun G _ ↦ mul_nonneg (atomWeight_nonneg _ _ _) (hX G)

theorem expectation_mono {lam : ℝ} {n : ℕ}
    {X Y : SimpleGraph (Fin n) → ℝ} (hXY : ∀ G, X G ≤ Y G) :
    expectation lam n X ≤ expectation lam n Y := by
  exact Finset.sum_le_sum fun G _ ↦
    mul_le_mul_of_nonneg_left (hXY G) (atomWeight_nonneg _ _ _)

theorem expectation_add (lam : ℝ) (n : ℕ)
    (X Y : SimpleGraph (Fin n) → ℝ) :
    expectation lam n (fun G ↦ X G + Y G) =
      expectation lam n X + expectation lam n Y := by
  simp [expectation, mul_add, Finset.sum_add_distrib]

theorem expectation_sub (lam : ℝ) (n : ℕ)
    (X Y : SimpleGraph (Fin n) → ℝ) :
    expectation lam n (fun G ↦ X G - Y G) =
      expectation lam n X - expectation lam n Y := by
  simp [expectation, mul_sub, Finset.sum_sub_distrib]

theorem expectation_mul_const (lam : ℝ) (n : ℕ)
    (X : SimpleGraph (Fin n) → ℝ) (a : ℝ) :
    expectation lam n (fun G ↦ X G * a) = expectation lam n X * a := by
  simp [expectation, ← mul_assoc, Finset.sum_mul]

theorem expectation_const_mul (lam : ℝ) (n : ℕ)
    (a : ℝ) (X : SimpleGraph (Fin n) → ℝ) :
    expectation lam n (fun G ↦ a * X G) = a * expectation lam n X := by
  simp_rw [mul_comm a, expectation_mul_const]

theorem expectation_indicator (lam : ℝ) (n : ℕ)
    (P : SimpleGraph (Fin n) → Prop) :
    expectation lam n (fun G ↦ if P G then 1 else 0) = probability lam n P := by
  classical
  rw [probability_eq_sum]
  unfold expectation
  apply Finset.sum_congr rfl
  intro G _
  split <;> simp_all

/-- Disjoint decomposition of an event by the value of a finite-valued statistic. -/
theorem probability_sum_fibers {ι : Type*} [DecidableEq ι]
    (lam : ℝ) (n : ℕ) (s : Finset ι) (f : SimpleGraph (Fin n) → ι)
    (R : SimpleGraph (Fin n) → Prop) :
    probability lam n (fun G ↦ f G ∈ s ∧ R G) =
      ∑ i ∈ s, probability lam n (fun G ↦ f G = i ∧ R G) := by
  simp only [probability_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro G _
  by_cases hR : R G
  · simp only [hR, and_true]
    rw [Finset.sum_ite_eq]
  · simp [hR]

theorem expectation_finset_sum {ι : Type*} (lam : ℝ) (n : ℕ)
    (s : Finset ι) (X : ι → SimpleGraph (Fin n) → ℝ) :
    expectation lam n (fun G ↦ ∑ i ∈ s, X i G) =
      ∑ i ∈ s, expectation lam n (X i) := by
  simp only [expectation, Finset.mul_sum]
  exact Finset.sum_comm

/-- First moment of a finite count of events. -/
theorem expectation_card_filter {ι : Type*} (lam : ℝ) (n : ℕ)
    (s : Finset ι) (P : ι → SimpleGraph (Fin n) → Prop) :
    expectation lam n (fun G ↦ ((s.filter fun i ↦ P i G).card : ℝ)) =
      ∑ i ∈ s, probability lam n (P i) := by
  have hcount : (fun G ↦ ((s.filter fun i ↦ P i G).card : ℝ)) =
      (fun G ↦ ∑ i ∈ s, if P i G then (1 : ℝ) else 0) := by
    funext G
    rw [← Finset.sum_filter]
    simp
  rw [hcount, expectation_finset_sum]
  simp only [expectation_indicator]

/-- An exact factorial-second-moment identity indexed by distinct witnesses. -/
theorem expectation_card_filter_factorial {ι : Type*} (lam : ℝ) (n : ℕ)
    (s : Finset ι) (P : ι → SimpleGraph (Fin n) → Prop) :
    expectation lam n (fun G ↦
      ((s.filter fun i ↦ P i G).card : ℝ) *
        (((s.filter fun i ↦ P i G).card : ℝ) - 1)) =
      ∑ ij ∈ s.offDiag, probability lam n (fun G ↦ P ij.1 G ∧ P ij.2 G) := by
  have hcount : (fun G ↦ ((s.filter fun i ↦ P i G).card : ℝ) *
        (((s.filter fun i ↦ P i G).card : ℝ) - 1)) =
      (fun G ↦ ((s.offDiag.filter fun ij ↦ P ij.1 G ∧ P ij.2 G).card : ℝ)) := by
    funext G
    have hsets : s.offDiag.filter (fun ij ↦ P ij.1 G ∧ P ij.2 G) =
        (s.filter fun i ↦ P i G).offDiag := by
      ext ij
      simp only [Finset.mem_filter, Finset.mem_offDiag]
      tauto
    rw [hsets, Finset.offDiag_card, Nat.cast_sub (Nat.le_mul_self _), Nat.cast_mul]
    ring
  rw [hcount]
  convert expectation_card_filter lam n s.offDiag
    (fun ij G ↦ P ij.1 G ∧ P ij.2 G) using 1
  congr 1
  funext G
  congr 1
  congr 1
  ext ij
  simp only [Finset.mem_filter]

/-- Finite Markov inequality, stated without division. -/
theorem threshold_mul_probability_le_expectation {lam t : ℝ} {n : ℕ}
    {X : SimpleGraph (Fin n) → ℝ} (hX : ∀ G, 0 ≤ X G) :
    t * probability lam n (fun G ↦ t ≤ X G) ≤ expectation lam n X := by
  classical
  rw [probability_eq_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro G _
  by_cases hG : t ≤ X G
  · simp only [hG, ↓reduceIte]
    nlinarith [atomWeight_nonneg lam n G]
  · simp only [hG, ↓reduceIte, mul_zero]
    exact mul_nonneg (atomWeight_nonneg _ _ _) (hX G)

/-- Finite Markov inequality. -/
theorem probability_ge_le_expectation_div {lam t : ℝ} {n : ℕ}
    {X : SimpleGraph (Fin n) → ℝ} (ht : 0 < t) (hX : ∀ G, 0 ≤ X G) :
    probability lam n (fun G ↦ t ≤ X G) ≤ expectation lam n X / t := by
  rw [le_div_iff₀ ht]
  simpa [mul_comm] using threshold_mul_probability_le_expectation hX (t := t)

/-- Variance in the finite labelled-graph probability space. -/
def variance (lam : ℝ) (n : ℕ) (X : SimpleGraph (Fin n) → ℝ) : ℝ :=
  expectation lam n (fun G ↦ (X G - expectation lam n X) ^ 2)

theorem variance_eq_second_moment_sub (lam : ℝ) (n : ℕ)
    (X : SimpleGraph (Fin n) → ℝ) :
    variance lam n X = expectation lam n (fun G ↦ X G ^ 2) -
      expectation lam n X ^ 2 := by
  unfold variance
  have hexp : (fun G ↦ (X G - expectation lam n X) ^ 2) =
      (fun G ↦ X G ^ 2 - 2 * expectation lam n X * X G +
        expectation lam n X ^ 2) := by
    funext G
    ring
  rw [hexp, expectation_add, expectation_sub, expectation_const_mul,
    expectation_const]
  ring

/-- Chebyshev's inequality for the event that a real variable is at most one. -/
theorem probability_le_one_le_variance {lam : ℝ} {n : ℕ}
    (X : SimpleGraph (Fin n) → ℝ) (hmean : 1 < expectation lam n X) :
    probability lam n (fun G ↦ X G ≤ 1) ≤
      variance lam n X / (expectation lam n X - 1) ^ 2 := by
  have hthreshold : 0 < (expectation lam n X - 1) ^ 2 := by positivity
  calc
    probability lam n (fun G ↦ X G ≤ 1) ≤
        probability lam n (fun G ↦
          (expectation lam n X - 1) ^ 2 ≤
            (X G - expectation lam n X) ^ 2) := by
      apply probability_mono
      intro G hG
      have hdiff : 0 ≤ 1 - X G := by linarith
      nlinarith [mul_nonneg (sub_nonneg.mpr hmean.le) hdiff,
        sq_nonneg (1 - X G)]
    _ ≤ variance lam n X / (expectation lam n X - 1) ^ 2 :=
      probability_ge_le_expectation_div hthreshold (fun G ↦ sq_nonneg _)

/-- A factorial-second-moment bound gives a quantitative probability of
having at least two objects.  No independence assumption is hidden here. -/
theorem probability_count_lt_two_le {lam : ℝ} {n : ℕ}
    (X : SimpleGraph (Fin n) → ℕ)
    (hmean : 1 < expectation lam n (fun G ↦ (X G : ℝ)))
    (hfactor : expectation lam n (fun G ↦ (X G : ℝ) * ((X G : ℝ) - 1)) ≤
      expectation lam n (fun G ↦ (X G : ℝ)) ^ 2) :
    probability lam n (fun G ↦ X G < 2) ≤
      expectation lam n (fun G ↦ (X G : ℝ)) /
        (expectation lam n (fun G ↦ (X G : ℝ)) - 1) ^ 2 := by
  have hvar : variance lam n (fun G ↦ (X G : ℝ)) ≤
      expectation lam n (fun G ↦ (X G : ℝ)) := by
    have hpoint : (fun G ↦ (X G : ℝ) * ((X G : ℝ) - 1)) =
        (fun G ↦ (X G : ℝ) ^ 2 - (X G : ℝ)) := by
      funext G
      ring
    rw [hpoint, expectation_sub] at hfactor
    rw [variance_eq_second_moment_sub]
    linarith
  calc
    probability lam n (fun G ↦ X G < 2) =
        probability lam n (fun G ↦ (X G : ℝ) ≤ 1) := by
      congr 1
      funext G
      apply propext
      norm_cast
      omega
    _ ≤ variance lam n (fun G ↦ (X G : ℝ)) /
        (expectation lam n (fun G ↦ (X G : ℝ)) - 1) ^ 2 :=
      probability_le_one_le_variance _ hmean
    _ ≤ _ := div_le_div_of_nonneg_right hvar (sq_nonneg _)

end

end Erdos745
