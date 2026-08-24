/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace Erdos1118

def IsEntire (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f

def IsNonconstantEntire (f : ℂ → ℂ) : Prop :=
  IsEntire f ∧ ∃ x y, f x ≠ f y

def exceptionalSet (f : ℂ → ℂ) (c : ℝ) : Set ℂ :=
  {z | c < ‖f z‖}

def HasFiniteArea (f : ℂ → ℂ) (c : ℝ) : Prop :=
  volume (exceptionalSet f c) ≠ ∞

noncomputable def maximumModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup ((fun z : ℂ ↦ ‖f z‖) '' Metric.sphere (0 : ℂ) r)

noncomputable def growthIntegrand (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  r / Real.log (Real.log (maximumModulus f r))

def GrowthIntegralConverges (f : ℂ → ℂ) : Prop :=
  ∃ R > 0,
    (∀ r, R ≤ r → 0 < Real.log (Real.log (maximumModulus f r))) ∧
    IntegrableOn (growthIntegrand f) (Set.Ioi R)

def thresholdSet (f : ℂ → ℂ) : Set ℝ :=
  {c | 0 < c ∧ HasFiniteArea f c}

def ClosedThresholdWitness (m : ℝ) : Prop :=
  ∃ f : ℂ → ℂ, IsNonconstantEntire f ∧ thresholdSet f = Set.Ici m

def OpenThresholdWitness (m : ℝ) : Prop :=
  ∃ f : ℂ → ℂ, IsNonconstantEntire f ∧ thresholdSet f = Set.Ioi m

theorem erdos_1118 :
    (∀ (f : ℂ → ℂ) (c : ℝ),
      Erdos1118.IsNonconstantEntire f → Erdos1118.HasFiniteArea f c → Erdos1118.GrowthIntegralConverges f) ∧ (∀ φ : ℝ → ℝ,
      Monotone φ → (∀ r, 0 ≤ r → 0 < φ r) →
      MeasureTheory.IntegrableOn (fun r : ℝ ↦ r / φ r) (Set.Ioi 0) →
      ∃ (f : ℂ → ℂ) (c C R : ℝ),
        Erdos1118.IsNonconstantEntire f ∧ 0 < c ∧ Erdos1118.HasFiniteArea f c ∧ 0 < C ∧ 0 < R ∧
          ∀ r, R ≤ r →
            Real.log (Real.log (Erdos1118.maximumModulus f r)) ≤ C * φ r) ∧ (∀ m : ℝ, 0 < m → Erdos1118.ClosedThresholdWitness m ∧ Erdos1118.OpenThresholdWitness m) := by
  sorry

end Erdos1118
