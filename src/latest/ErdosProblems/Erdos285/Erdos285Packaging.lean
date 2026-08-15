/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Erdős Problem 285: packaging the asymptotic input

This file isolates the formal-conjectures wrapper from the number-theoretic theorem.
The hypothesis of `erdos_285_of_uniform_ratio` is the internal uniform-ratio result:
on indices represented by `S`, the least possible final denominator, divided by
`e / (e - 1) * (k + 1)`, tends to one.  Off `S` the ratio is completed by the
constant one.  The proof below converts this ratio limit into the error function
and exact equality requested by the upstream statement.
-/

open Filter
open scoped Topology Real

namespace Erdos285

noncomputable section

attribute [local instance] Classical.propDecidable

/--
The exact upstream statement follows from the completed uniform-ratio theorem.

The long hypothesis is deliberately an argument of this theorem.  Thus this file
contains only the packaging implication, and does not postulate the analytic and
number-theoretic content of Martin's theorem.
-/
theorem erdos_285_of_uniform_ratio
    (uniform_ratio :
      ∀ᵉ (f : ℕ → ℕ)
      (S : Set ℕ)
      (hS : S = {k | ∃ (n : Fin k.succ → ℕ), StrictMono n ∧ 0 ∉ Set.range n ∧
        1 = ∑ i, (1 : ℝ) / n i })
      (h : ∀ k ∈ S,
        IsLeast
          { n (Fin.last k) | (n : Fin k.succ → ℕ) (_ : StrictMono n) (_ : 0 ∉ Set.range n)
            (_ : 1 = ∑ i, (1 : ℝ) / n i) }
          (f k)),
      Tendsto
        (fun k : ℕ ↦
          if k ∈ S then
            (f k : ℝ) / (rexp 1 / (rexp 1 - 1) * (k + 1 : ℕ))
          else 1)
        atTop (nhds 1)) :
    True ↔ ∀ᵉ (f : ℕ → ℕ)
    (S : Set ℕ)
    (hS : S = {k | ∃ (n : Fin k.succ → ℕ), StrictMono n ∧ 0 ∉ Set.range n ∧
      1 = ∑ i, (1 : ℝ) / n i })
    (h : ∀ k ∈ S,
      IsLeast
        { n (Fin.last k) | (n : Fin k.succ → ℕ) (_ : StrictMono n) (_ : 0 ∉ Set.range n)
          (_ : 1 = ∑ i, (1 : ℝ) / n i) }
        (f k)),
    ∃ (o : ℕ → ℝ) (_ : o =o[atTop] (1 : ℕ → ℝ)),
      ∀ k ∈ S, f k = (1 + o k) * rexp 1 / (rexp 1 - 1) * (k + 1) := by
  constructor
  · intro _ f S hS h
    have hratio := uniform_ratio f S hS h
    let o : ℕ → ℝ := fun k ↦
      (if k ∈ S then
          (f k : ℝ) / (rexp 1 / (rexp 1 - 1) * (k + 1 : ℕ))
        else 1) - 1
    refine ⟨o, ?_, ?_⟩
    · apply (Asymptotics.isLittleO_one_iff ℝ).2
      have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
      simpa [o] using hratio.sub hone
    · intro k hk
      dsimp [o]
      rw [if_pos hk]
      have hexp : rexp 1 - 1 ≠ 0 :=
        ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.2 zero_lt_one))
      have hk1 : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      norm_num [div_eq_mul_inv, hexp, hk1]
      field_simp [hexp, hk1]
  · intro _
    trivial

end

end Erdos285

#print axioms Erdos285.erdos_285_of_uniform_ratio
