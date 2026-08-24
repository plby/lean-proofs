/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

namespace Erdos553

def ThreeColorRamseyProperty (m N : ℕ) : Prop :=
  ∀ red blue : SimpleGraph (Fin N),
    ¬ (red.CliqueFree 3 ∧ blue.CliqueFree 3 ∧ (red ⊔ blue).IndepSetFree m)

noncomputable def threeColorRamseyNumber (m : ℕ) : ℕ :=
  sInf {N : ℕ | ThreeColorRamseyProperty m N}

end Erdos553

namespace Ramsey

def RamseyProperty (k l n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), ¬ (G.CliqueFree k ∧ G.IndepSetFree l)

end Ramsey

namespace Erdos553

noncomputable def twoColorRamseyNumber (m : ℕ) : ℕ :=
  sInf {N : ℕ | Ramsey.RamseyProperty 3 m N}

theorem erdos_553 :
    Tendsto
      (fun m : ℕ ↦
        (threeColorRamseyNumber m : ℝ) / (twoColorRamseyNumber m : ℝ))
      atTop atTop := by
  sorry

end Erdos553
