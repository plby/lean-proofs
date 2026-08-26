import Mathlib

open scoped BigOperators ProbabilityTheory Topology

namespace Erdos521

open Filter MeasureTheory ProbabilityTheory

noncomputable def polynomial (ε : ℕ → ℝ) (n : ℕ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (n + 1), Polynomial.C (ε k) * Polynomial.X ^ k

noncomputable def realRoots (ε : ℕ → ℝ) (n : ℕ) : Finset ℝ :=
  (polynomial ε n).roots.toFinset

noncomputable def rootCount (ε : ℕ → ℝ) (n : ℕ) : ℕ :=
  (realRoots ε n).card

noncomputable def signLaw : Measure ℝ :=
  Ber((1 : ℝ), (-1 : ℝ), ⟨1 / 2, by norm_num⟩)

instance : IsProbabilityMeasure signLaw := by
  unfold signLaw
  infer_instance

noncomputable def sequenceLaw : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun _ : ℕ ↦ signLaw

instance : IsProbabilityMeasure sequenceLaw := by
  unfold sequenceLaw
  infer_instance

noncomputable def normalizedRootCount (ε : ℕ → ℝ) (n : ℕ) : ℝ :=
  (rootCount ε n : ℝ) / Real.log n

def Conjecture : Prop :=
  ∀ᵐ ε ∂sequenceLaw, Tendsto (normalizedRootCount ε) atTop (𝓝 (2 / Real.pi))

theorem erdos521_oscillation :
    ∀ᵐ ε ∂sequenceLaw,
      liminf (fun n ↦ (normalizedRootCount ε n : EReal)) atTop = (1 / Real.pi : ℝ) ∧
      (2 / Real.pi : ℝ) ≤ limsup (fun n ↦ (normalizedRootCount ε n : EReal)) atTop := by
  sorry

theorem not_erdos_521 : ¬ Conjecture := by
  sorry

end Erdos521
