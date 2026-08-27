import ErdosProblems.Erdos4.FGKMTLawOperations

/-! Exact conditioning of a finite law on an event of positive mass. -/

open scoped BigOperators

namespace Erdos4.FGKMT.FiniteLaw

variable {Ω : Type*} [Fintype Ω]

noncomputable def condition (ν : FiniteLaw Ω) (E : Ω → Prop) [DecidablePred E]
    (o₀ : Ω) : FiniteLaw Ω :=
  normalize (fun o => if E o then ν.weight o else 0)
    (fun o => by split_ifs; exact ν.nonneg o; rfl) o₀

theorem restricted_weight_sum (ν : FiniteLaw Ω) (E : Ω → Prop) [DecidablePred E] :
    (∑ o, if E o then ν.weight o else 0) = ν.prob E := by
  classical
  unfold prob
  apply Finset.sum_congr rfl
  intro o _ho
  by_cases he : E o <;> simp [he]

theorem condition_weight (ν : FiniteLaw Ω) (E : Ω → Prop) [DecidablePred E]
    (o₀ o : Ω) (hE : ν.prob E ≠ 0) :
    (ν.condition E o₀).weight o = (if E o then ν.weight o else 0) / ν.prob E := by
  have hsum : (∑ o, if E o then ν.weight o else 0) ≠ 0 := by
    rw [restricted_weight_sum]
    exact hE
  rw [condition, normalize_weight _ _ _ _ hsum, restricted_weight_sum]

theorem condition_mean (ν : FiniteLaw Ω) (E : Ω → Prop) [DecidablePred E]
    (o₀ : Ω) (hE : ν.prob E ≠ 0) (f : Ω → ℝ) :
    (ν.condition E o₀).mean f = ν.mean (fun o => if E o then f o else 0) / ν.prob E := by
  unfold mean
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro o _ho
  rw [condition_weight ν E o₀ o hE]
  by_cases he : E o <;> simp [he, div_mul_eq_mul_div]

theorem condition_prob (ν : FiniteLaw Ω) (E F : Ω → Prop) [DecidablePred E]
    (o₀ : Ω) (hE : ν.prob E ≠ 0) :
    (ν.condition E o₀).prob F = ν.prob (fun o => E o ∧ F o) / ν.prob E := by
  classical
  rw [prob_eq_mean, condition_mean ν E o₀ hE]
  congr 1
  rw [prob_eq_mean]
  apply ν.mean_congr
  intro o
  by_cases he : E o <;> by_cases hf : F o <;> simp [he, hf]

theorem condition_support (ν : FiniteLaw Ω) (E : Ω → Prop) [DecidablePred E]
    (o₀ o : Ω) (hE : ν.prob E ≠ 0) (ho : 0 < (ν.condition E o₀).weight o) : E o := by
  rw [condition_weight ν E o₀ o hE] at ho
  by_contra he
  simp only [if_neg he, zero_div] at ho
  linarith

end Erdos4.FGKMT.FiniteLaw
