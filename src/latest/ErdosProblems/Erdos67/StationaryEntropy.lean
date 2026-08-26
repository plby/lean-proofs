import ErdosProblems.Erdos67.Entropy
import Mathlib.Tactic

/-!
# Finite entropy estimates for the stationary discrepancy argument

The exponential variational inequality is proved for finite probability vectors,
including vectors with zero coordinates. These are supporting inequalities, not
an assertion of the discrepancy theorem.
-/

open scoped BigOperators
open Finset

namespace Erdos67.FiniteEntropy

variable {α : Type*} [Fintype α]

/-- Finite relative entropy. Absolute continuity is supplied to theorems using it. -/
noncomputable def relativeEntropy (p q : FinProb α) : ℝ :=
  ∑ a, correctedKLTerm (p a) (q a)

theorem relativeEntropy_nonneg (p q : FinProb α)
    (hpq : ∀ a, 0 < p a → 0 < q a) :
    0 ≤ relativeEntropy p q := by
  exact Finset.sum_nonneg fun a _ ↦
    correctedKLTerm_nonneg (prob_nonneg p a) (prob_nonneg q a) (hpq a)

theorem relativeEntropy_eq_sum (p q : FinProb α) :
    relativeEntropy p q = ∑ a, p a * Real.log (p a / q a) := by
  unfold relativeEntropy correctedKLTerm
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [stdSimplex.sum_eq_one, stdSimplex.sum_eq_one]
  ring

theorem exponential_sum_pos (q : FinProb α) (F : α → ℝ) :
    0 < ∑ a, q a * Real.exp (F a) := by
  have hsome : ∃ a, 0 < q a := by
    by_contra! h
    have hz : ∀ a, q a = 0 := fun a ↦ le_antisymm (h a) (prob_nonneg q a)
    have hsum := stdSimplex.sum_eq_one q
    simp only [hz, Finset.sum_const_zero] at hsum
    norm_num at hsum
  obtain ⟨a, ha⟩ := hsome
  exact Finset.sum_pos' (fun b _ ↦ mul_nonneg (prob_nonneg q b) (Real.exp_pos _).le)
    ⟨a, Finset.mem_univ _, mul_pos ha (Real.exp_pos _)⟩

/-- The exponentially tilted probability vector. -/
noncomputable def exponentialTilt (q : FinProb α) (F : α → ℝ) : FinProb α :=
  ⟨fun a ↦ q a * Real.exp (F a) / (∑ b, q b * Real.exp (F b)), by
    constructor
    · intro a
      exact div_nonneg (mul_nonneg (prob_nonneg q a) (Real.exp_pos _).le)
        (exponential_sum_pos q F).le
    · rw [← Finset.sum_div, div_self (exponential_sum_pos q F).ne']⟩

theorem exponentialTilt_pos (q : FinProb α) (F : α → ℝ) (a : α)
    (ha : 0 < q a) : 0 < exponentialTilt q F a :=
  div_pos (mul_pos ha (Real.exp_pos _)) (exponential_sum_pos q F)

theorem relativeEntropy_exponentialTilt (p q : FinProb α) (F : α → ℝ)
    (hpq : ∀ a, 0 < p a → 0 < q a) :
    relativeEntropy p (exponentialTilt q F) = relativeEntropy p q -
      (∑ a, p a * F a) + Real.log (∑ a, q a * Real.exp (F a)) := by
  have hterm (a : α) :
      p a * Real.log (p a / exponentialTilt q F a) =
        p a * Real.log (p a / q a) - p a * F a +
          p a * Real.log (∑ b, q b * Real.exp (F b)) := by
    by_cases ha : p a = 0
    · simp [ha]
    have hpa : 0 < p a := (prob_nonneg p a).lt_of_ne' ha
    have hqa : 0 < q a := hpq a hpa
    have htilt : exponentialTilt q F a =
        q a * Real.exp (F a) / (∑ b, q b * Real.exp (F b)) := rfl
    rw [Real.log_div ha (exponentialTilt_pos q F a hqa).ne', htilt,
      Real.log_div (mul_pos hqa (Real.exp_pos _)).ne' (exponential_sum_pos q F).ne',
      Real.log_mul hqa.ne' (Real.exp_ne_zero _), Real.log_exp,
      Real.log_div ha hqa.ne']
    ring
  rw [relativeEntropy_eq_sum, relativeEntropy_eq_sum]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    stdSimplex.sum_eq_one, one_mul]

/-- Finite exponential variational inequality, with natural logarithms. -/
theorem expectation_le_relativeEntropy_add_log_exp (p q : FinProb α) (F : α → ℝ)
    (hpq : ∀ a, 0 < p a → 0 < q a) :
    (∑ a, p a * F a) ≤
      relativeEntropy p q + Real.log (∑ a, q a * Real.exp (F a)) := by
  have h := relativeEntropy_nonneg p (exponentialTilt q F)
    (fun a ha ↦ exponentialTilt_pos q F a (hpq a ha))
  rw [relativeEntropy_exponentialTilt p q F hpq] at h
  linarith

/-- The uniform probability vector on a nonempty finite type. -/
noncomputable def uniformVector [Nonempty α] : FinProb α :=
  ⟨fun _ ↦ (Fintype.card α : ℝ)⁻¹, by
    constructor
    · intro a
      positivity
    · simp [Fintype.card_ne_zero]⟩

theorem uniformVector_pos [Nonempty α] (a : α) :
    0 < uniformVector (α := α) a := by
  change 0 < (Fintype.card α : ℝ)⁻¹
  positivity

theorem uniformVector_apply [Nonempty α] (a : α) :
    uniformVector a = (Fintype.card α : ℝ)⁻¹ := rfl

theorem relativeEntropy_uniformVector [Nonempty α] (p : FinProb α) :
    relativeEntropy p uniformVector = Real.log (Fintype.card α) - entropy p := by
  have hterm (a : α) :
      p a * Real.log (p a / uniformVector (α := α) a) =
        p a * Real.log (p a) + p a * Real.log (Fintype.card α) := by
    by_cases ha : p a = 0
    · simp [ha]
    change p a * Real.log (p a / (Fintype.card α : ℝ)⁻¹) = _
    have hc : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    rw [Real.log_div ha (inv_ne_zero hc), Real.log_inv]
    ring
  rw [relativeEntropy_eq_sum]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, stdSimplex.sum_eq_one, one_mul]
  simp only [entropy, Real.negMulLog, neg_mul, Finset.sum_neg_distrib]
  ring

/-- The sharp cardinality bound needed for blocks of signs. -/
theorem entropy_le_log_card [Nonempty α] (p : FinProb α) :
    entropy p ≤ Real.log (Fintype.card α) := by
  have h := relativeEntropy_nonneg p uniformVector
    (fun a _ ↦ uniformVector_pos a)
  rw [relativeEntropy_uniformVector] at h
  linarith

variable {β : Type*} [Fintype β]

theorem relativeEntropy_marginal_product (p : FinProb (α × β)) :
    relativeEntropy p (product (fstMarginal p) (sndMarginal p)) = mutualInfo p := by
  rw [mutualInfo_eq_jointProductKL]
  rfl

/-- A rowwise exponential-moment estimate converts mutual information into an
expectation bound. The reference law keeps the marginals and makes them independent. -/
theorem joint_expectation_le_mutualInfo_add (p : FinProb (α × β))
    (F : α → β → ℝ) (K : ℝ)
    (hF : ∀ a, (∑ b, sndMarginal p b * Real.exp (F a b)) ≤ Real.exp K) :
    (∑ z, p z * F z.1 z.2) ≤ mutualInfo p + K := by
  have habs : ∀ z : α × β, 0 < p z →
      0 < product (fstMarginal p) (sndMarginal p) z := by
    rintro ⟨a, b⟩ hz
    exact mul_pos (hz.trans_le (joint_le_fstMarginal p a b))
      (hz.trans_le (joint_le_sndMarginal p a b))
  have h := expectation_le_relativeEntropy_add_log_exp p
    (product (fstMarginal p) (sndMarginal p)) (fun z ↦ F z.1 z.2) habs
  rw [relativeEntropy_marginal_product] at h
  apply h.trans
  apply add_le_add le_rfl
  apply (Real.log_le_iff_le_exp (exponential_sum_pos _ _)).mpr
  rw [Fintype.sum_prod_type]
  change (∑ a, ∑ b, (fstMarginal p a * sndMarginal p b) * Real.exp (F a b)) ≤ _
  simp_rw [mul_assoc, ← Finset.mul_sum]
  calc
    (∑ a, fstMarginal p a * ∑ b, sndMarginal p b * Real.exp (F a b)) ≤
        ∑ a, fstMarginal p a * Real.exp K :=
      Finset.sum_le_sum fun a _ ↦
        mul_le_mul_of_nonneg_left (hF a) (prob_nonneg (fstMarginal p) a)
    _ = Real.exp K := by rw [← Finset.sum_mul, stdSimplex.sum_eq_one, one_mul]

end Erdos67.FiniteEntropy
