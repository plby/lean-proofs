/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos1166

open Filter MeasureTheory
open scoped BigOperators ENNReal

abbrev Site := ℤ × ℤ

abbrev Direction := Fin 4

def directionStep (d : Direction) : Site :=
  match d.1 with
  | 0 => (1, 0)
  | 1 => (-1, 0)
  | 2 => (0, 1)
  | _ => (0, -1)

def simpleRandomWalk (ω : ℕ → Direction) (n : ℕ) : Site :=
  ∑ j ∈ Finset.range n, directionStep (ω j)

noncomputable def incrementLaw : Measure (ℕ → Direction) :=
  Measure.infinitePi fun _ : ℕ ↦ (PMF.uniformOfFintype Direction).toMeasure

noncomputable def simpleRandomWalkLaw : Measure (ℕ → Site) :=
  incrementLaw.map simpleRandomWalk

def visitedSites (s : ℕ → Site) (n : ℕ) : Finset Site :=
  (Finset.range (n + 1)).image s

def localTime (s : ℕ → Site) (n : ℕ) (x : Site) : ℕ :=
  ((Finset.range (n + 1)).filter fun j ↦ s j = x).card

def maxLocalTime (s : ℕ → Site) (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sup fun j ↦ localTime s n (s j)

def favoriteSites (s : ℕ → Site) (n : ℕ) : Finset Site :=
  (visitedSites s n).filter fun x ↦ localTime s n x = maxLocalTime s n

def favoriteUnion (s : ℕ → Site) (n : ℕ) : Finset Site :=
  (Finset.range (n + 1)).biUnion (favoriteSites s)

def HasCumulativeFavoriteLogSqBound (s : ℕ → Site) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
    ((favoriteUnion s n).card : ℝ) ≤ C * Real.log (n : ℝ) ^ 2

theorem erdos_1166 :
    ∀ᵐ s ∂simpleRandomWalkLaw, HasCumulativeFavoriteLogSqBound s := by
  sorry

end Erdos1166
