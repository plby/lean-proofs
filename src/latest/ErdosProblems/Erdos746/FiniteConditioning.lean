import ErdosProblems.Erdos746.Model
import Mathlib.Data.Finset.Sigma
import Mathlib.Tactic

/-!
# Uniform conditioning over equal finite fibers

This file records the elementary finite conditioning estimate used by the
sprinkling argument.  Its sample space is a dependent sum whose fibers all
have the same positive cardinality.  Thus uniform measure on the dependent
sum first chooses a base point uniformly and then chooses uniformly in its
fiber.
-/

open scoped BigOperators

namespace Erdos746

noncomputable section

/-- Uniform probability on a dependent sum of equally large, nonempty fibers
is the average of the uniform probabilities in its fibers. -/
theorem uniformProbability_sigma_eq_average
    {P : Type*} [Fintype P] [Nonempty P]
    {F : P → Type*} [∀ p, Fintype (F p)]
    (C : ℕ) (hC : 0 < C) (hcard : ∀ p, Fintype.card (F p) = C)
    (event : (Σ p, F p) → Prop) :
    uniformProbability event =
      (∑ p : P, uniformProbability (fun x : F p ↦ event ⟨p, x⟩)) /
        Fintype.card P := by
  classical
  have hnum :
      (Finset.univ.filter event).card =
        ∑ p : P, (Finset.univ.filter (fun x : F p ↦ event ⟨p, x⟩)).card := by
    rw [show (Finset.univ : Finset (Σ p, F p)) =
        Finset.univ.sigma (fun p : P ↦ (Finset.univ : Finset (F p))) by
      ext z
      simp]
    rw [Finset.filter_sigma' Finset.univ
      (fun p : P ↦ (Finset.univ : Finset (F p)))
      (fun p x ↦ event ⟨p, x⟩), Finset.card_sigma]
  have htotal : Fintype.card (Σ p, F p) = Fintype.card P * C := by
    rw [Fintype.card_sigma]
    simp_rw [hcard]
    simp
  have hC0 : (C : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hC)
  have hP0 : (Fintype.card P : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [uniformProbability, hnum, htotal]
  simp_rw [uniformProbability, hcard]
  push_cast
  rw [← Finset.sum_div]
  field_simp [hC0, hP0]

/-- Finite law of total probability in the form needed for sprinkling.

Over a good base point the conditional bad probability is at most `err`; over
a bad base point it is at most one.  Averaging these two bounds gives the
probability of a bad base point plus `err`. -/
theorem uniformProbability_sigma_le_bad_base_add
    {P : Type*} [Fintype P] [Nonempty P]
    {F : P → Type*} [∀ p, Fintype (F p)]
    (C : ℕ) (hC : 0 < C) (hcard : ∀ p, Fintype.card (F p) = C)
    (good : P → Prop) (bad : (Σ p, F p) → Prop) (err : ℝ)
    (herr : 0 ≤ err)
    (hfiber : ∀ p, good p →
      uniformProbability (fun x : F p ↦ bad ⟨p, x⟩) ≤ err) :
    uniformProbability bad ≤
      uniformProbability (fun p ↦ ¬ good p) + err := by
  classical
  rw [uniformProbability_sigma_eq_average C hC hcard bad]
  let q : P → ℝ := fun p ↦
    uniformProbability (fun x : F p ↦ bad ⟨p, x⟩)
  have hpoint (p : P) : q p ≤ (if ¬ good p then 1 else 0) + err := by
    by_cases hp : good p
    · simp only [hp, not_true_eq_false, if_false, zero_add]
      exact hfiber p hp
    · have hq := uniformProbability_le_one
          (fun x : F p ↦ bad ⟨p, x⟩)
      have hone : (1 : ℝ) ≤ 1 + err := le_add_of_nonneg_right herr
      simpa [q, hp] using hq.trans hone
  have hsum :
      (∑ p : P, q p) ≤
        (∑ p : P, if ¬ good p then (1 : ℝ) else 0) +
          Fintype.card P * err := by
    calc
      (∑ p : P, q p) ≤
          ∑ p : P, ((if ¬ good p then (1 : ℝ) else 0) + err) :=
        Finset.sum_le_sum fun p _ ↦ hpoint p
      _ = (∑ p : P, if ¬ good p then (1 : ℝ) else 0) +
          Fintype.card P * err := by
        rw [Finset.sum_add_distrib]
        simp
  have hPpos : (0 : ℝ) < Fintype.card P := by
    exact_mod_cast Fintype.card_pos
  have hP0' : (Fintype.card P : ℝ) ≠ 0 := ne_of_gt hPpos
  calc
    (∑ p : P, uniformProbability (fun x : F p ↦ bad ⟨p, x⟩)) /
          Fintype.card P = (∑ p : P, q p) / Fintype.card P := rfl
    _ ≤ ((∑ p : P, if ¬ good p then (1 : ℝ) else 0) +
          Fintype.card P * err) / Fintype.card P :=
      div_le_div_of_nonneg_right hsum hPpos.le
    _ = uniformProbability (fun p ↦ ¬ good p) + err := by
      rw [uniformProbability]
      have hcount :
          ((Finset.univ.filter (fun p ↦ ¬ good p)).card : ℝ) =
            ∑ p : P, if ¬ good p then (1 : ℝ) else 0 := by
        calc
          ((Finset.univ.filter (fun p ↦ ¬ good p)).card : ℝ) =
              ∑ p ∈ Finset.univ.filter (fun p ↦ ¬ good p), (1 : ℝ) := by
            simp
          _ = ∑ p : P, if ¬ good p then (1 : ℝ) else 0 := by
            rw [Finset.sum_filter]
      field_simp [hP0']
      rw [← hcount]
      apply congrArg (fun s : Finset P ↦
        (s.card : ℝ) + (Fintype.card P : ℝ) * err)
      ext p
      simp

end

end Erdos746
