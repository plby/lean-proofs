import ErdosProblems.Erdos4.RestrictedProductNorm

/-!
# Finite products of rank-one deletion projections

Symmetry and idempotence imply contraction by an elementary sum-of-squares
identity. The product kernel inherits both properties. This applies to
arbitrary mixtures of the true and ideal one-prime projections.
-/

open scoped BigOperators

namespace Erdos4.ProjectionKernel

variable {A : Type*} [Fintype A] [DecidableEq A]

noncomputable def kernel (u : A → ℝ) (a b : A) : ℝ :=
  (if a = b then 1 else 0) - u a * u b

omit [Fintype A] in
theorem kernel_symm (u : A → ℝ) (a b : A) : kernel u a b = kernel u b a := by
  simp only [kernel, eq_comm, mul_comm]

theorem kernel_idempotent (u : A → ℝ) (hu : ∑ a, u a ^ 2 = 1) (a c : A) :
    (∑ b, kernel u a b * kernel u b c) = kernel u a c := by
  have hlast : (∑ b, (u a * u b) * (u b * u c)) = u a * u c * ∑ b, u b ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun b _hb => by ring)
  simp only [kernel, sub_mul, mul_sub, Finset.sum_sub_distrib]
  rw [hlast, hu]
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
  simp

noncomputable def action (K : A → A → ℝ) (v : A → ℝ) (a : A) : ℝ :=
  ∑ b, K a b * v b

omit [DecidableEq A] in
theorem action_adjoint (K : A → A → ℝ) (hK : ∀ a b, K a b = K b a)
    (v w : A → ℝ) :
    (∑ a, v a * action K w a) = ∑ a, action K v a * w a := by
  unfold action
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _ha
  apply Finset.sum_congr rfl
  intro b _hb
  rw [hK b a]
  ring

omit [DecidableEq A] in
theorem action_idempotent (K : A → A → ℝ)
    (hK : ∀ a c, (∑ b, K a b * K b c) = K a c) (v : A → ℝ) :
    action K (action K v) = action K v := by
  funext a
  unfold action
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _hc
  have hh : (∑ b, K a b * (K b c * v c)) = (∑ b, K a b * K b c) * v c := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun b _hb => by ring)
  rw [hh, hK a c]

omit [DecidableEq A] in
theorem action_energy_eq_dot (K : A → A → ℝ)
    (hKs : ∀ a b, K a b = K b a)
    (hKi : ∀ a c, (∑ b, K a b * K b c) = K a c) (v : A → ℝ) :
    (∑ a, action K v a ^ 2) = ∑ a, v a * action K v a := by
  have hh := action_adjoint K hKs v (action K v)
  rw [action_idempotent K hKi v] at hh
  simpa only [pow_two] using hh.symm

omit [DecidableEq A] in
/-- A finite symmetric idempotent kernel is contractive. -/
theorem action_energy_le (K : A → A → ℝ)
    (hKs : ∀ a b, K a b = K b a)
    (hKi : ∀ a c, (∑ b, K a b * K b c) = K a c) (v : A → ℝ) :
    (∑ a, action K v a ^ 2) ≤ ∑ a, v a ^ 2 := by
  have hnonneg : 0 ≤ ∑ a, (v a - action K v a) ^ 2 :=
    Finset.sum_nonneg (fun a _ha => sq_nonneg _)
  have heq : (∑ a, (v a - action K v a) ^ 2) =
      (∑ a, v a ^ 2) - 2 * (∑ a, v a * action K v a) + ∑ a, action K v a ^ 2 := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun a _ha => by ring)
  rw [heq, ← action_energy_eq_dot K hKs hKi v] at hnonneg
  linarith

omit [DecidableEq A] in
theorem form_sq_le_energy (K : A → A → ℝ)
    (hKs : ∀ a b, K a b = K b a)
    (hKi : ∀ a c, (∑ b, K a b * K b c) = K a c) (v w : A → ℝ) :
    (∑ a, v a * action K w a) ^ 2 ≤ (∑ a, v a ^ 2) * ∑ a, w a ^ 2 := by
  exact (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v (action K w)).trans
    (mul_le_mul_of_nonneg_left (action_energy_le K hKs hKi w)
      (Finset.sum_nonneg (fun a _ha => sq_nonneg _)))

variable {P : Type*} [Fintype P] [DecidableEq P]

noncomputable def tensor (u : P → A → ℝ) (a b : P → A) : ℝ :=
  ∏ p, kernel (u p) (a p) (b p)

omit [DecidableEq P] in
theorem tensor_symm (u : P → A → ℝ) (a b : P → A) : tensor u a b = tensor u b a := by
  exact Finset.prod_congr rfl (fun p _hp => kernel_symm (u p) (a p) (b p))

theorem tensor_idempotent (u : P → A → ℝ) (hu : ∀ p, ∑ a, u p a ^ 2 = 1)
    (a c : P → A) : (∑ b, tensor u a b * tensor u b c) = tensor u a c := by
  unfold tensor
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun p b => kernel (u p) (a p) b * kernel (u p) b (c p))]
  exact Finset.prod_congr rfl (fun p _hp => kernel_idempotent (u p) (hu p) (a p) (c p))

/-- All mixtures of unit-normal local projections have the same exact
coefficient-energy contraction bound. -/
theorem tensor_form_sq_le_energy (u : P → A → ℝ) (hu : ∀ p, ∑ a, u p a ^ 2 = 1)
    (v w : (P → A) → ℝ) :
    (∑ a, v a * action (tensor u) w a) ^ 2 ≤ (∑ a, v a ^ 2) * ∑ a, w a ^ 2 :=
  form_sq_le_energy (tensor u) (tensor_symm u) (tensor_idempotent u hu) v w

end Erdos4.ProjectionKernel
