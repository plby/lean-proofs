/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 994.
https://www.erdosproblems.com/forum/thread/994

Informal authors:
- J. M. Marstrand

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos994.md
-/
/-
This is a Lean formalization of the literal simultaneous-quantifier statement displayed
in Erdős Problem 994.

The historical Khintchine conjecture is normally read with the measurable set fixed
first: `∀ E, ∀ᵐ α, ...`.  Marstrand disproved that assertion with one fixed set, a much
deeper result.  The database display instead ends with "for almost all α ... for all
E", namely `∀ᵐ α, ∀ E, ...`.  The definitions below record both orders explicitly and
the main theorem keeps the displayed order.  Its negation has a short diagonal proof:
for each α, delete the countable orbit `{fract (k * α)}` from `(0, 1)`.  The resulting
measurable set still has measure one but is never visited.

See `tex/994.tex` for the complete proof, the machine-checked quantifier comparison,
and a detailed reconstruction of the historical fixed-set construction.
-/

import Mathlib

open Filter MeasureTheory Set
open scoped Topology

namespace Erdos994

attribute [local instance] Classical.propDecidable

/-- The normalized number of visits of the fractional parts
`fract (k * α)`, `1 ≤ k ≤ n`, to `E`.

At `n = 0` this is `0`, by the usual field convention for division by zero. -/
noncomputable def visitAverage (E : Set ℝ) (α : ℝ) (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.Icc 1 n,
      if Int.fract ((k : ℝ) * α) ∈ E then (1 : ℝ) else 0) / (n : ℝ)

/-- The visit averages for `E` and `α` converge to the Lebesgue measure of `E`. -/
def HasExpectedLimit (E : Set ℝ) (α : ℝ) : Prop :=
  Tendsto (visitAverage E α) atTop (𝓝 (volume E).toReal)

/-- A parameter `α` is simultaneously good if the expected limit holds for every
Lebesgue measurable subset of `(0, 1)`. -/
def SimultaneouslyGood (α : ℝ) : Prop :=
  ∀ E : Set ℝ, MeasurableSet E → E ⊆ Ioo (0 : ℝ) 1 → HasExpectedLimit E α

/-- The simultaneous reading of the assertion displayed in Erdős Problem 994. -/
def KhintchineSimultaneous : Prop :=
  ∀ᵐ α : ℝ, SimultaneouslyGood α

/-- The conventional fixed-set quantifier order of Khintchine's historical conjecture.
Here the exceptional null set is allowed to depend on `E`. -/
def KhintchineFixedSet : Prop :=
  ∀ E : Set ℝ, MeasurableSet E → E ⊆ Ioo (0 : ℝ) 1 →
    ∀ᵐ α : ℝ, HasExpectedLimit E α

/-- The simultaneous assertion implies the fixed-set assertion.  Keeping this lemma in
the formal development prevents the two logically different quantifier orders from
being conflated. -/
lemma simultaneous_implies_fixedSet : KhintchineSimultaneous → KhintchineFixedSet := by
  intro h E hE hEI
  filter_upwards [h] with α hα
  exact hα E hE hEI

/-- The countable positive fractional-part orbit of `α`. -/
def orbit (α : ℝ) : Set ℝ :=
  Set.range fun j : ℕ => Int.fract (((j + 1 : ℕ) : ℝ) * α)

/-- Delete the positive orbit of `α` from `(0, 1)`. -/
def counterexampleSet (α : ℝ) : Set ℝ :=
  Ioo (0 : ℝ) 1 \ orbit α

lemma orbit_countable (α : ℝ) : (orbit α).Countable := by
  exact Set.countable_range _

lemma orbit_measurableSet (α : ℝ) : MeasurableSet (orbit α) := by
  exact (orbit_countable α).measurableSet

lemma counterexampleSet_measurableSet (α : ℝ) : MeasurableSet (counterexampleSet α) := by
  exact measurableSet_Ioo.diff (orbit_measurableSet α)

lemma counterexampleSet_subset (α : ℝ) : counterexampleSet α ⊆ Ioo (0 : ℝ) 1 := by
  exact Set.sdiff_subset

lemma orbit_measure_zero (α : ℝ) : volume (orbit α) = 0 := by
  exact (orbit_countable α).measure_zero volume

lemma counterexampleSet_measure (α : ℝ) : volume (counterexampleSet α) = 1 := by
  rw [counterexampleSet, measure_sdiff_null (orbit_measure_zero α), Real.volume_Ioo]
  norm_num

lemma counterexampleSet_measure_toReal (α : ℝ) :
    (volume (counterexampleSet α)).toReal = 1 := by
  rw [counterexampleSet_measure]
  norm_num

lemma fract_mul_mem_orbit (α : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    Int.fract ((k : ℝ) * α) ∈ orbit α := by
  refine ⟨k - 1, ?_⟩
  have h : k - 1 + 1 = k := Nat.sub_add_cancel hk
  simp only [h]

lemma fract_mul_not_mem_counterexampleSet (α : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    Int.fract ((k : ℝ) * α) ∉ counterexampleSet α := by
  intro h
  exact h.2 (fract_mul_mem_orbit α hk)

lemma visitAverage_counterexampleSet (α : ℝ) (n : ℕ) :
    visitAverage (counterexampleSet α) α n = 0 := by
  unfold visitAverage
  rw [Finset.sum_eq_zero]
  · simp
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    simp [fract_mul_not_mem_counterexampleSet α hk.1]

lemma counterexampleSet_tendsto_zero (α : ℝ) :
    Tendsto (visitAverage (counterexampleSet α) α) atTop (𝓝 0) := by
  have hfun : visitAverage (counterexampleSet α) α = fun _ : ℕ => (0 : ℝ) := by
    funext n
    exact visitAverage_counterexampleSet α n
  rw [hfun]
  exact tendsto_const_nhds

/-- Every real parameter has a measurable set of measure one for which all visit
averages vanish.  This is the pointwise diagonal counterexample. -/
theorem exists_counterexample (α : ℝ) :
    ∃ E : Set ℝ,
      MeasurableSet E ∧ E ⊆ Ioo (0 : ℝ) 1 ∧ volume E = 1 ∧
        Tendsto (visitAverage E α) atTop (𝓝 0) ∧ ¬HasExpectedLimit E α := by
  refine ⟨counterexampleSet α, counterexampleSet_measurableSet α,
    counterexampleSet_subset α, counterexampleSet_measure α,
    counterexampleSet_tendsto_zero α, ?_⟩
  intro h
  have hzero : (0 : ℝ) = 1 := by
    exact tendsto_nhds_unique (counterexampleSet_tendsto_zero α)
      (by simpa [HasExpectedLimit, counterexampleSet_measure_toReal] using h)
  norm_num at hzero

theorem not_simultaneouslyGood (α : ℝ) : ¬SimultaneouslyGood α := by
  intro h
  obtain ⟨E, hE, hEI, _hmeasure, _hzero, hbad⟩ := exists_counterexample α
  exact hbad (h E hE hEI)

/-- **Erdős Problem 994 (negative answer, literal simultaneous reading).**

It is false that for almost every `α`, the fractional-part visit averages have
the expected limit simultaneously for every measurable `E ⊆ (0, 1)`. -/
theorem erdos_994 : ¬KhintchineSimultaneous := by
  intro h
  obtain ⟨α, hα⟩ := h.exists
  exact not_simultaneouslyGood α hα

#print axioms erdos_994

end Erdos994
