import Mathlib

noncomputable section


namespace Erdos55

open scoped Classical in
def IsPositiveNatSet (A : Set ℕ) : Prop :=
  ∀ ⦃a : ℕ⦄, a ∈ A → 0 < a

end Erdos55

namespace Erdos55

open scoped Classical in
def PositiveNatSet := {A : Set ℕ // IsPositiveNatSet A}

namespace PositiveNatSet

open scoped Classical in
instance : SetLike PositiveNatSet ℕ where
  coe A := A.1
  coe_injective A B h := Subtype.ext h

end PositiveNatSet

end Erdos55

namespace Erdos55

open scoped Classical in
def monochromaticSums {r : ℕ} (A : Set ℕ) (color : A → Fin r) : Set ℕ :=
  {n | ∃ i : Fin r, ∃ s : Finset A,
    (∀ a ∈ s, color a = i) ∧ (∑ a ∈ s, (a : ℕ)) = n}

end Erdos55

namespace Erdos55

open scoped Classical in
def IsMonochromaticSum {r : ℕ} (A : Set ℕ) (color : A → Fin r) (n : ℕ) : Prop :=
  n ∈ monochromaticSums A color

end Erdos55

namespace Erdos55

open scoped Classical in
def RamseyComplete (r : ℕ) (A : Set ℕ) : Prop :=
  ∀ color : A → Fin r, ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    IsMonochromaticSum A color n

end Erdos55

namespace Erdos55

open scoped Classical in
noncomputable def countUpTo (A : Set ℕ) (N : ℕ) : ℕ :=
  by
    classical
    exact ((Finset.Icc 1 N).filter (fun a ↦ a ∈ A)).card

end Erdos55

namespace Erdos55

open scoped Classical in
def CFPUpperBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 2 ≤ r →
    ∃ A : PositiveNatSet, RamseyComplete r A ∧
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (countUpTo A N : ℝ) ≤ C * (r : ℝ) * Real.log (N : ℝ) ^ 2

end Erdos55

namespace Erdos55

open scoped Classical in
def CFPLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ, 2 ≤ r → ∀ A : PositiveNatSet,
    (∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (countUpTo A N : ℝ) ≤ c * (r : ℝ) * Real.log (N : ℝ) ^ 2) →
    ¬ RamseyComplete r A

end Erdos55

namespace Erdos55

open scoped Classical in
def ConlonFoxPhamResolution : Prop :=
  CFPUpperBound ∧ CFPLowerBound

end Erdos55

namespace Erdos55

open scoped Classical in
theorem erdos_55 : ConlonFoxPhamResolution := by
  sorry

end Erdos55

end
