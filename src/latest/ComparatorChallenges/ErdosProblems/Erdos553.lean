import Mathlib

open Filter Real
open scoped Topology

noncomputable section


namespace Erdos553

open scoped Classical in
def ThreeColorRamseyProperty (m N : ℕ) : Prop :=
  ∀ red blue : SimpleGraph (Fin N),
    ¬ (red.CliqueFree 3 ∧ blue.CliqueFree 3 ∧ (red ⊔ blue).IndepSetFree m)

end Erdos553

namespace Erdos553

open scoped Classical in
def threeColorRamseyNumber (m : ℕ) : ℕ :=
  sInf {N : ℕ | ThreeColorRamseyProperty m N}

end Erdos553

namespace Ramsey

open scoped Classical in
def RamseyProperty (k l n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), ¬ (G.CliqueFree k ∧ G.IndepSetFree l)

end Ramsey

namespace Erdos553

open scoped Classical in
def twoColorRamseyNumber (m : ℕ) : ℕ :=
  sInf {N : ℕ | Ramsey.RamseyProperty 3 m N}

end Erdos553

namespace Erdos553

open scoped Classical in
def Problem553 : Prop :=
  Tendsto
    (fun m : ℕ ↦
      (threeColorRamseyNumber m : ℝ) / (twoColorRamseyNumber m : ℝ))
    atTop atTop

end Erdos553

namespace Erdos553

open scoped Classical in
theorem erdos_553 : Problem553 := by
  sorry

end Erdos553

end
