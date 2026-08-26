/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The probability space and distinct-root counts in Erdős Problem 521.
Informal sources: Paul Erdős; the problem statement curated by Thomas Bloom.
Formal author: Codex.
https://www.erdosproblems.com/521
-/
import ErdosProblems.Erdos521.Records
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.EReal.Basic
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Independence.InfinitePi

open scoped BigOperators ProbabilityTheory Topology

namespace Erdos521

open Filter MeasureTheory ProbabilityTheory

/-- The polynomial of degree `n` formed from the first `n+1` coefficients. -/
noncomputable def polynomial (ε : ℕ → ℝ) (n : ℕ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (n + 1), Polynomial.C (ε k) * Polynomial.X ^ k

theorem polynomial_eval (ε : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    (polynomial ε n).eval x = powerSum ε (n + 1) x := by
  simp [polynomial, powerSum, Polynomial.eval_finsetSum]

theorem polynomial_eval_zero (ε : ℕ → ℝ) (n : ℕ) :
    (polynomial ε n).eval 0 = ε 0 := by
  rw [polynomial_eval]
  simp [powerSum, Finset.sum_range_succ']

theorem polynomial_ne_zero (ε : ℕ → ℝ) (n : ℕ) (h : ε 0 ≠ 0) :
    polynomial ε n ≠ 0 := by
  intro hp
  have he := polynomial_eval_zero ε n
  rw [hp, Polynomial.eval_zero] at he
  exact h he.symm

/-- Distinct real roots: `toFinset` removes multiplicities. -/
noncomputable def realRoots (ε : ℕ → ℝ) (n : ℕ) : Finset ℝ :=
  (polynomial ε n).roots.toFinset

/-- Number of distinct real roots. The zero polynomial cannot occur for signs. -/
noncomputable def rootCount (ε : ℕ → ℝ) (n : ℕ) : ℕ := (realRoots ε n).card

/-- Number of distinct real roots in the closed interval `[-1,1]`. -/
noncomputable def interiorRootCount (ε : ℕ → ℝ) (n : ℕ) : ℕ := by
  classical
  exact ((realRoots ε n).filter fun x ↦ x ∈ Set.Icc (-1 : ℝ) 1).card

theorem mem_realRoots (ε : ℕ → ℝ) (n : ℕ) (h : ε 0 ≠ 0) (x : ℝ) :
    x ∈ realRoots ε n ↔ powerSum ε (n + 1) x = 0 := by
  simp only [realRoots, Multiset.mem_toFinset,
    Polynomial.mem_roots (polynomial_ne_zero ε n h), Polynomial.IsRoot, polynomial_eval]

theorem interiorRootCount_le (ε : ℕ → ℝ) (n : ℕ) :
    interiorRootCount ε n ≤ rootCount ε n := by
  classical
  exact Finset.card_filter_le _ _

/-- The deterministic root-count equality supplied by a cone record. -/
theorem rootCount_eq_interior_of_record (ε : ℕ → ℝ) (m : ℕ)
    (h : CoefficientRecord ε m) (hlead : ε (2 * m + 1) ≠ 0) :
    rootCount ε (2 * m + 1) = interiorRootCount ε (2 * m + 1) := by
  classical
  unfold rootCount interiorRootCount
  congr 1
  symm
  apply Finset.filter_eq_self.mpr
  intro x hx
  have hz : powerSum ε (2 * m + 2) x = 0 := by
    have hp := Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp hx)
    exact (polynomial_eval ε (2 * m + 1) x).symm.trans hp
  have hbound : |x| ≤ 1 := by
    by_contra hh
    exact coefficientRecord_no_exterior_root ε m h hlead x (lt_of_not_ge hh) hz
  exact abs_le.mp hbound

/-- A fair sign law; the two atoms have equal weight. -/
noncomputable def signLaw : Measure ℝ :=
  Ber((1 : ℝ), (-1 : ℝ), ⟨1 / 2, by norm_num⟩)

instance : IsProbabilityMeasure signLaw := by
  unfold signLaw
  infer_instance

theorem signLaw_one : signLaw.real ({1} : Set ℝ) = 1 / 2 := by
  rw [signLaw, bernoulliMeasure_real_apply_of_mem_of_notMem]
  · measurability
  · simp
  · norm_num

theorem signLaw_neg_one : signLaw.real ({-1} : Set ℝ) = 1 / 2 := by
  rw [signLaw, bernoulliMeasure_real_apply_of_notMem_of_mem]
  · change 1 - (1 / 2 : ℝ) = 1 / 2
    norm_num
  · measurability
  · norm_num
  · simp

/-- One infinite iid sequence is sampled, and all degrees use its prefixes. -/
noncomputable def sequenceLaw : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun _ : ℕ ↦ signLaw

instance : IsProbabilityMeasure sequenceLaw := by
  unfold sequenceLaw
  infer_instance

theorem ae_signLaw : ∀ᵐ x ∂signLaw, x = 1 ∨ x = -1 := by
  rw [ae_iff]
  simp [signLaw, bernoulliMeasure_def]

theorem ae_sequence_signs : ∀ᵐ ε ∂sequenceLaw, ∀ n, ε n = 1 ∨ ε n = -1 := by
  rw [ae_all_iff]
  intro n
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ signLaw) n).quasiMeasurePreserving.ae
    ae_signLaw

theorem sequenceLaw_map_eval (n : ℕ) :
    sequenceLaw.map (fun ε ↦ ε n) = signLaw := by
  exact Measure.infinitePi_map_eval (fun _ : ℕ ↦ signLaw) n

theorem independent_coefficients :
    iIndepFun (fun n : ℕ ↦ fun ε : ℕ → ℝ ↦ ε n) sequenceLaw := by
  exact iIndepFun_infinitePi (fun _ ↦ measurable_id)

theorem ae_record_rootCount_eq :
    ∀ᵐ ε ∂sequenceLaw, ∀ m, CoefficientRecord ε m →
      rootCount ε (2 * m + 1) = interiorRootCount ε (2 * m + 1) := by
  filter_upwards [ae_sequence_signs] with ε hε
  intro m hm
  apply rootCount_eq_interior_of_record ε m hm
  rcases hε (2 * m + 1) with hsign | hsign <;> simp [hsign]

/-- The normalized number of distinct real roots. Values at `n = 0,1` have
no effect on the limits at infinity. -/
noncomputable def normalizedRootCount (ε : ℕ → ℝ) (n : ℕ) : ℝ :=
  (rootCount ε n : ℝ) / Real.log n

/-- The almost-sure convergence conjecture in the symmetric-sign formulation
of Erdős Problem 521, disproved by `not_erdos521` in the entry point. -/
def Conjecture : Prop :=
  ∀ᵐ ε ∂sequenceLaw, Tendsto (normalizedRootCount ε) atTop (𝓝 (2 / Real.pi))

/-- The stronger claim in the selected writeup, proved in `Oscillation.lean`.
Extended-real limits retain the intended meaning even when the limsup is infinite. -/
def ClaimedOscillation : Prop :=
  ∀ᵐ ε ∂sequenceLaw,
    liminf (fun n ↦ (normalizedRootCount ε n : EReal)) atTop = (1 / Real.pi : ℝ) ∧
    (2 / Real.pi : ℝ) ≤ limsup (fun n ↦ (normalizedRootCount ε n : EReal)) atTop

end Erdos521
