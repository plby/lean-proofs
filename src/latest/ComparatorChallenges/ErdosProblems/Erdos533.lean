/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Formalization of the negative answer to Erdős Problem 533.

The mathematical construction is the `p = 3`, `ℓ = 1` specialization of
the complex Bollobás--Erdős graph of Liu, Reiher, Sharifzadeh, and Staden.
-/

import ErdosProblems.Erdos615Construction

open Filter SimpleGraph
open Set MeasureTheory
open scoped Classical ENNReal NNReal Pointwise Topology BigOperators

syntax (name := answerSyntax533) "answer(" term ")" : term
macro_rules | `(answer($t)) => `($t)

namespace Erdos533

/-! ## The complex sphere used by the LRSS construction -/

/-- The unit sphere in a nonzero finite-dimensional complex Euclidean space.
The parameter is shifted by one so that the sphere is nonempty also at `k = 0`. -/
abbrev ComplexSphere (k : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℂ (Fin (k + 1))) 1

instance complexSphereNonempty (k : ℕ) : Nonempty (ComplexSphere k) :=
  ⟨⟨EuclideanSpace.single 0 1, by simp [ComplexSphere, Metric.mem_sphere]⟩⟩

/-- Surface measure on `ComplexSphere k`, regarded as a bundled finite measure. -/
noncomputable def complexSphereFiniteMeasure (k : ℕ) :
    MeasureTheory.FiniteMeasure (ComplexSphere k) :=
  ⟨MeasureTheory.Measure.toSphere MeasureTheory.volume, inferInstance⟩

/-- Normalized surface measure on the complex unit sphere. -/
noncomputable def complexSphereProbability (k : ℕ) :
    MeasureTheory.ProbabilityMeasure (ComplexSphere k) :=
  (complexSphereFiniteMeasure k).normalize

@[simp] theorem complexSphereProbability_univ (k : ℕ) :
    (complexSphereProbability k : MeasureTheory.Measure (ComplexSphere k)) Set.univ = 1 := by
  exact MeasureTheory.measure_univ

/-! ## A two-set concentration lemma on a real sphere -/

/-- Brunn--Minkowski applied to the two truncated cones over `A` and `-B`.
If both sets have more than `(d / 2)^h` of the spherical surface measure,
then some pair has distance greater than `d`.  This two-set form is the
concentration input used to find the three approximate rotations. -/

theorem erdos_533 : answer(False) ↔
    ∀ δ : ℝ, 0 < δ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ∀ G : SimpleGraph (Fin n), G.CliqueFree 5 →
        δ * (n : ℝ) ^ 2 ≤ G.edgeFinset.card →
          ∃ S : Finset (Fin n), c * n ≤ (S.card : ℝ) ∧
            G.CliqueFreeOn (S : Set (Fin n)) 3 := by
  sorry

