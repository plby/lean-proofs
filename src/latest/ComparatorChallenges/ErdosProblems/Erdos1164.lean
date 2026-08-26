/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter MeasureTheory

namespace Erdos1165

abbrev Direction := Fin 4

abbrev Point := ℤ × ℤ

abbrev StepPath := ℕ → Direction

abbrev WalkPath := ℕ → Point

def directionVector : Direction → Point
  | ⟨0, _⟩ => (1, 0)
  | ⟨1, _⟩ => (-1, 0)
  | ⟨2, _⟩ => (0, 1)
  | ⟨3, _⟩ => (0, -1)

noncomputable def fairStep : Measure Direction :=
  ProbabilityTheory.uniformOn Set.univ

noncomputable def fairSteps : Measure StepPath :=
  Measure.infinitePi fun _ : ℕ ↦ fairStep

def trajectory (ω : StepPath) (n : ℕ) : Point :=
  ∑ j ∈ Finset.range n, directionVector (ω j)

noncomputable def simpleRandomWalk : Measure WalkPath :=
  fairSteps.map trajectory

end Erdos1165

namespace Erdos1164

abbrev Point := Erdos1165.Point

abbrev WalkPath := Erdos1165.WalkPath

noncomputable abbrev walkLaw : Measure WalkPath := Erdos1165.simpleRandomWalk

/-- The closed Euclidean lattice disc of integer radius. -/
def latticeDisc (r : ℕ) : Set Point :=
  {x | x.1 ^ 2 + x.2 ^ 2 ≤ (r : ℤ) ^ 2}

/-- Every lattice point in the disc has been visited by time `n`. -/
def CoversBy (s : WalkPath) (n r : ℕ) : Prop :=
  ∀ x ∈ latticeDisc r, ∃ k ≤ n, s k = x

/-- The largest completely covered integer disc radius. -/
noncomputable def coveredRadius (s : WalkPath) (n : ℕ) : ℕ := by
  classical
  exact ((Finset.range (n + 1)).filter (CoversBy s n)).sup id

/-- The covered-disc log-radius has order `sqrt (log n)` in probability. -/
theorem erdos_1164 :
    ∀ ε : ℝ, 0 < ε → ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧
      ∀ᶠ n : ℕ in atTop,
        walkLaw.real {s | Real.log (coveredRadius s n : ℝ) <
          a * Real.sqrt (Real.log (n : ℝ))} < ε ∧
        walkLaw.real {s | b * Real.sqrt (Real.log (n : ℝ)) <
          Real.log (coveredRadius s n : ℝ)} < ε := by
  sorry

end Erdos1164
