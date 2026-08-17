import Mathlib

open scoped BigOperators Finset Topology
open Filter Function Finset Fintype

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos190

structure AP (N k : ℕ) where
  start : ℕ
  step : ℕ
  step_pos : 0 < step
  isLt : ∀ i : Fin k, start + i.1 * step < N

end Erdos190

namespace Erdos190.AP

def term (P : AP N k) (i : Fin k) : Fin N :=
  ⟨P.start + i.1 * P.step, P.isLt i⟩

end Erdos190.AP

namespace Erdos190

def Monochromatic (c : Fin N → C) (P : AP N k) : Prop :=
  ∀ i j : Fin k, c (P.term i) = c (P.term j)

end Erdos190

namespace Erdos190

def Rainbow (c : Fin N → C) (P : AP N k) : Prop :=
  Injective (c ∘ P.term)

end Erdos190

namespace Erdos190

def Good (k N : ℕ) : Prop :=
  ∀ (C : Type) (_ : Fintype C) (c : Fin N → C),
    ∃ P : AP N k, Monochromatic c P ∨ Rainbow c P

end Erdos190

namespace Erdos190

noncomputable def H (k : ℕ) : ℕ :=
  sInf {N : ℕ | 0 < N ∧ Good k N}

end Erdos190

namespace Erdos190

theorem erdos_190 :
    Tendsto (fun k : ℕ => (H k : ℝ) ^ (1 / (k : ℝ)) / (k : ℝ))
      atTop atTop := by
  sorry

end Erdos190

end
