/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter Function

namespace Erdos190

structure AP (N k : ℕ) where
  start : ℕ
  step : ℕ
  step_pos : 0 < step
  isLt : ∀ i : Fin k, start + i.1 * step < N

namespace AP

def term (P : AP N k) (i : Fin k) : Fin N :=
  ⟨P.start + i.1 * P.step, P.isLt i⟩

end AP

def Monochromatic (c : Fin N → C) (P : AP N k) : Prop :=
  ∀ i j : Fin k, c (P.term i) = c (P.term j)

def Rainbow (c : Fin N → C) (P : AP N k) : Prop :=
  Injective (c ∘ P.term)

def Good (k N : ℕ) : Prop :=
  ∀ (C : Type) (_ : Fintype C) (c : Fin N → C),
    ∃ P : AP N k, Monochromatic c P ∨ Rainbow c P

noncomputable def H (k : ℕ) : ℕ :=
  sInf {N : ℕ | 0 < N ∧ Good k N}

theorem erdos_190 :
    Tendsto (fun k : ℕ => (H k : ℝ) ^ (1 / (k : ℝ)) / (k : ℝ))
      atTop atTop := by
  sorry

end Erdos190
