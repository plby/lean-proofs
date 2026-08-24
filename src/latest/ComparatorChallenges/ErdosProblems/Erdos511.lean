/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos511

def componentsIn (s : Set ℂ) : Set (Set ℂ) :=
  {C | ∃ x : s, C = Subtype.val '' (connectedComponent x : Set s)}

def lemniscate (p : Polynomial ℂ) : Set ℂ :=
  {z : ℂ | ‖p.eval z‖ < 1}

def largeComponents (p : Polynomial ℂ) (d : ℝ) : Set (Set ℂ) :=
  {C | C ∈ componentsIn (lemniscate p) ∧ d < Metric.diam C}

def HasAtLeastLargeComponents
    (p : Polynomial ℂ) (d : ℝ) (N : ℕ) : Prop :=
  ∃ C : Fin N → Set ℂ,
    Function.Injective C ∧ ∀ i, C i ∈ largeComponents p d

theorem not_erdos_511 :
    ¬ (∀ d : ℝ, 1 < d →
      ∃ B : ℕ, ∀ p : Polynomial ℂ, p.Monic →
        ¬ HasAtLeastLargeComponents p d (B + 1)) := by
  sorry

end Erdos511
