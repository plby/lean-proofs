/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTFiniteTransform
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!
# Tensorizing a finite local weighted pushforward

Two code states per label are allowed. The weights may have either
sign; the identity follows entirely from finite distributivity and
the equality indicator of the reconstructed assignment.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α σ β γ : Type*} [Fintype α] [Fintype σ] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq σ]

omit [Fintype β] [Fintype γ] in
theorem finite_double_product_fiber_sum (decode : α → β → γ → σ)
    (w : α → β → γ → ℝ) (a : α → β) (b : α → γ) (F : (α → σ) → ℝ) :
    (∑ s : α → σ, (∏ q, if decode q (a q) (b q) = s q then w q (a q) (b q) else 0) *
      F s) = (∏ q, w q (a q) (b q)) * F (fun q => decode q (a q) (b q)) := by
  classical
  simp only [Fintype.prod_ite_zero, ← funext_iff, ite_mul, zero_mul]
  simp

theorem finite_double_product_pushforward (decode : α → β → γ → σ)
    (w : α → β → γ → ℝ) (K : α → σ → ℝ)
    (hlocal : ∀ q s, (∑ a : β, ∑ b : γ,
      if decode q a b = s then w q a b else 0) = K q s)
    (F : (α → σ) → ℝ) :
    (∑ s : α → σ, (∏ q, K q (s q)) * F s) =
      ∑ a : α → β, ∑ b : α → γ,
        (∏ q, w q (a q) (b q)) * F (fun q => decode q (a q) (b q)) := by
  classical
  let T := fun (s : α → σ) (a : α → β) (b : α → γ) =>
    (∏ q, if decode q (a q) (b q) = s q then w q (a q) (b q) else 0) * F s
  have hexpand (s : α → σ) : (∏ q, K q (s q)) * F s = ∑ a, ∑ b, T s a b := by
    simp_rw [← hlocal]
    rw [Fintype.prod_sum (fun q a => ∑ b : γ,
      if decode q a b = s q then w q a b else 0), Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _ha
    rw [Fintype.prod_sum (fun q b =>
      if decode q (a q) b = s q then w q (a q) b else 0), Finset.sum_mul]
  calc
    _ = ∑ s, ∑ a, ∑ b, T s a b := by simp only [hexpand]
    _ = ∑ a, ∑ s, ∑ b, T s a b := by rw [Finset.sum_comm]
    _ = ∑ a, ∑ b, ∑ s, T s a b := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _ha
      apply Finset.sum_congr rfl
      intro b _hb
      exact finite_double_product_fiber_sum decode w a b F

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.finite_double_product_pushforward
