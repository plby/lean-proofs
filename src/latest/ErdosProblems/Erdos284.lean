/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 284.
https://www.erdosproblems.com/forum/thread/284

Informal authors:
- Ernest S. Croot III

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos284.md
-/
import ErdosProblems.Erdos284.Final

/-!
# Erdős Problem 284

For a positive number `k` of terms, let `f(k)` be the greatest possible
first denominator in a strictly increasing `k`-term representation of one
as a sum of unit fractions.  This file states that definition literally and
proves

`f(k) / k → 1 / (exp 1 - 1)`.

The internal development uses `k + 1` terms in order to avoid carrying a
positivity proof through every occurrence of `Fin k`.  The bridge theorem
`originalFirstDenominators_succ` verifies that the public definition below is
exactly the shifted internal one.
-/

open Filter
open scoped BigOperators Topology Real

namespace Erdos284

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The representation appearing verbatim in the problem, with exactly `k`
terms. -/
def OriginalRepresentation (k : ℕ) (n : Fin k → ℕ) : Prop :=
  StrictMono n ∧ 0 ∉ Set.range n ∧ 1 = ∑ i, (1 : ℝ) / n i

/-- The possible values of the first denominator in a `k`-term
representation.  For `k = 0` this set is empty. -/
def OriginalFirstDenominators (k : ℕ) : Set ℕ :=
  {m | ∃ (hk : 0 < k) (n : Fin k → ℕ),
    OriginalRepresentation k n ∧ n ⟨0, hk⟩ = m}

/-- The extremal function `f(k)` in the statement of Erdős Problem 284. -/
def originalErdosF (k : ℕ) : ℕ :=
  sSup (OriginalFirstDenominators k)

/-- The literal `k + 1`-term denominator set is the internally used set. -/
theorem originalFirstDenominators_succ (k : ℕ) :
    OriginalFirstDenominators (k + 1) = FirstDenominators k := by
  ext m
  rw [mem_firstDenominators]
  constructor
  · rintro ⟨hk, n, hn, hm⟩
    have hn' : Representation k n := by
      simpa only [OriginalRepresentation, Representation,
        Nat.succ_eq_add_one] using hn
    refine ⟨n, hn', ?_⟩
    simpa using hm
  · rintro ⟨n, hn, hm⟩
    refine ⟨Nat.zero_lt_succ k, n, ?_, ?_⟩
    · simpa only [OriginalRepresentation, Representation,
        Nat.succ_eq_add_one] using hn
    · simpa using hm

@[simp] theorem originalErdosF_succ (k : ℕ) :
    originalErdosF (k + 1) = erdosF k := by
  rw [originalErdosF, erdosF, originalFirstDenominators_succ]

/-- Thus `originalErdosF` is eventually the greatest possible first
denominator, rather than merely a supremum with a default value. -/
theorem eventually_originalErdosF_isMaximal :
    ∀ᶠ k : ℕ in atTop,
      IsGreatest (OriginalFirstDenominators k) (originalErdosF k) := by
  have hshift :=
    (Filter.tendsto_sub_atTop_nat 1).eventually
      eventually_erdosF_isMaximal_proved
  filter_upwards [eventually_ge_atTop 1, hshift] with k hk hmax
  have hksub : k - 1 + 1 = k := Nat.sub_add_cancel hk
  rw [← hksub]
  simpa only [originalFirstDenominators_succ, originalErdosF_succ,
    IsMaximalFirstDenominator] using hmax

/-- **Resolution of Erdős Problem 284.**  If `f(k)` is the maximal first
denominator of a strictly increasing `k`-term Egyptian-fraction
representation of one, then `f(k) / k` tends to `1 / (e - 1)`. -/
theorem erdos_284 :
    Tendsto (fun k : ℕ ↦ (originalErdosF k : ℝ) / (k : ℝ))
      atTop (nhds (1 / (Real.exp 1 - 1))) := by
  apply (Filter.tendsto_add_atTop_iff_nat 1).mp
  simpa only [originalErdosF_succ, Nat.cast_add, Nat.cast_one,
    erdosConstant] using erdos_284_limit

end

end Erdos284

#print axioms Erdos284.erdos_284
