/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

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

noncomputable instance : IsProbabilityMeasure fairStep := by
  unfold fairStep
  infer_instance

noncomputable def fairSteps : Measure StepPath :=
  Measure.infinitePi fun _ : ℕ ↦ fairStep

def trajectory (ω : StepPath) (n : ℕ) : Point :=
  ∑ j ∈ Finset.range n, directionVector (ω j)

noncomputable def simpleRandomWalk : Measure WalkPath :=
  fairSteps.map trajectory

def pathPrefix (s : WalkPath) (n : ℕ) : Fin (n + 1) → Point :=
  fun j ↦ s j

def localTimePrefix {n : ℕ} (u : Fin (n + 1) → Point) (x : Point) : ℕ :=
  (Finset.univ.filter fun j ↦ u j = x).card

def visitedPrefix {n : ℕ} (u : Fin (n + 1) → Point) : Finset Point :=
  Finset.univ.image u

def maxLocalTimePrefix {n : ℕ} (u : Fin (n + 1) → Point) : ℕ :=
  (visitedPrefix u).sup (localTimePrefix u)

def favoritePrefix {n : ℕ} (u : Fin (n + 1) → Point) : Finset Point :=
  (visitedPrefix u).filter fun x ↦ localTimePrefix u x = maxLocalTimePrefix u

def favoriteSites (s : WalkPath) (n : ℕ) : Finset Point :=
  favoritePrefix (pathPrefix s n)

def favoriteCount (s : WalkPath) (n : ℕ) : ℕ :=
  (favoriteSites s n).card

def favoriteEvent (r : ℕ) : Set WalkPath :=
  {s | ∃ᶠ n in atTop, favoriteCount s n = r}

theorem erdos_1165 (r : ℕ) (hr : 3 ≤ r) :
    simpleRandomWalk (favoriteEvent r) = if r = 3 then 1 else 0 := by
  sorry

end Erdos1165
