import Mathlib

open Polynomial Set Topology Metric Filter

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos511

def componentsIn (s : Set ℂ) : Set (Set ℂ) :=
  {C | ∃ x : s, C = Subtype.val '' (connectedComponent x : Set s)}

end Erdos511

namespace Erdos511

def lemniscate (p : Polynomial ℂ) : Set ℂ :=
  {z : ℂ | ‖p.eval z‖ < 1}

end Erdos511

namespace Erdos511

def largeComponents (p : Polynomial ℂ) (d : ℝ) : Set (Set ℂ) :=
  {C | C ∈ componentsIn (lemniscate p) ∧ d < Metric.diam C}

end Erdos511

namespace Erdos511

def HasAtLeastLargeComponents
    (p : Polynomial ℂ) (d : ℝ) (N : ℕ) : Prop :=
  ∃ C : Fin N → Set ℂ,
    Function.Injective C ∧ ∀ i, C i ∈ largeComponents p d

end Erdos511

namespace Erdos511

def Erdos511Bounded : Prop :=
  ∀ d : ℝ, 1 < d →
    ∃ B : ℕ, ∀ p : Polynomial ℂ, p.Monic →
      ¬ HasAtLeastLargeComponents p d (B + 1)

end Erdos511

namespace Erdos511

theorem erdos_511 : ¬ Erdos511Bounded := by
  sorry

end Erdos511

end
