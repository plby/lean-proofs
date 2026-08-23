/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

noncomputable section


namespace Erdos54

open scoped Classical in
def PositiveNatSet (A : Set ℕ) : Prop :=
  ∀ a : ↑A, 0 < (a : ℕ)

end Erdos54

namespace Erdos54

open scoped Classical in
abbrev Coloring (A : Set ℕ) (r : ℕ) := ↑A → Fin r

end Erdos54

namespace Erdos54

open scoped Classical in
def MonochromaticSum (A : Set ℕ) (r : ℕ) (color : Coloring A r) (n : ℕ) : Prop :=
  ∃ s : Finset ↑A,
    (∃ c : Fin r, ∀ a ∈ s, color a = c) ∧
      ∑ a ∈ s, (a : ℕ) = n

end Erdos54

namespace Erdos54

open scoped Classical in
def RamseyComplete (r : ℕ) (A : Set ℕ) : Prop :=
  ∀ color : Coloring A r, ∃ threshold : ℕ, ∀ n ≥ threshold,
    MonochromaticSum A r color n

end Erdos54

namespace Erdos54

open scoped Classical in
abbrev RamseyTwoComplete (A : Set ℕ) : Prop := RamseyComplete 2 A

end Erdos54

namespace Erdos54

open scoped Classical in
noncomputable def countUpTo (A : Set ℕ) (N : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 N).filter fun a ↦ a ∈ A).card

end Erdos54

namespace Erdos54

open scoped Classical in
def HasLogSquaredCountingBound (A : Set ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
    (countUpTo A N : ℝ) ≤ C * (Real.log (N : ℝ)) ^ 2

end Erdos54

namespace Erdos54

open scoped Classical in
def ConlonFoxPhamUpperBoundTwo : Prop :=
  ∃ A : Set ℕ,
    PositiveNatSet A ∧ RamseyTwoComplete A ∧ HasLogSquaredCountingBound A

end Erdos54

namespace Erdos54

open scoped Classical in
theorem erdos_54 : ConlonFoxPhamUpperBoundTwo := by
  sorry

end Erdos54

end
