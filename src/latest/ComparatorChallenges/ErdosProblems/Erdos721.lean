/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos721

open Filter
open Classical
open scoped BigOperators Topology

def HasMonochromaticAP (n l : ℕ) (color : ℕ → Fin 2) (hue : Fin 2) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ a + (l - 1) * d < n ∧
    ∀ i : Fin l, color (a + i.val * d) = hue

def ForcesW3 (n k : ℕ) : Prop :=
  ∀ color : ℕ → Fin 2,
    HasMonochromaticAP n 3 color 0 ∨
      HasMonochromaticAP n k color 1

theorem exists_forcesW3 (k : ℕ) : ∃ n, ForcesW3 n k := by
  sorry

noncomputable def W3 (k : ℕ) : ℕ :=
  by
    classical
    exact Nat.find (exists_forcesW3 k)

def HunterLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ᶠ k : ℕ in atTop,
      Real.exp (c * (Real.log k) ^ 2 / Real.log (Real.log k)) ≤ (W3 k : ℝ)

def QuasipolynomialUpperBound : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ᶠ k : ℕ in atTop,
      (W3 k : ℝ) ≤ Real.exp (C * (Real.log k) ^ 9)

def SubexponentialUpperBound : Prop :=
  ∃ γ : ℝ, 0 < γ ∧ γ < 1 ∧
    ∀ᶠ k : ℕ in atTop,
      (W3 k : ℝ) < Real.exp ((k : ℝ) ^ γ)

def Erdos721Resolution : Prop :=
  HunterLowerBound ∧ QuasipolynomialUpperBound ∧ SubexponentialUpperBound

theorem erdos721Resolution : Erdos721Resolution := by
  sorry

end Erdos721
