import Mathlib

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace Erdos55

def IsPositiveNatSet (A : Set ℕ) : Prop :=
  ∀ ⦃a : ℕ⦄, a ∈ A → 0 < a

end Erdos55

namespace Erdos55

def PositiveNatSet := {A : Set ℕ // IsPositiveNatSet A}

namespace PositiveNatSet

instance : SetLike PositiveNatSet ℕ where
  coe A := A.1
  coe_injective A B h := Subtype.ext h

end PositiveNatSet

end Erdos55

namespace Erdos55

def monochromaticSums {r : ℕ} (A : Set ℕ) (color : A → Fin r) : Set ℕ :=
  {n | ∃ i : Fin r, ∃ s : Finset A,
    (∀ a ∈ s, color a = i) ∧ (∑ a ∈ s, (a : ℕ)) = n}

end Erdos55

namespace Erdos55

def IsMonochromaticSum {r : ℕ} (A : Set ℕ) (color : A → Fin r) (n : ℕ) : Prop :=
  n ∈ monochromaticSums A color

end Erdos55

namespace Erdos55

def RamseyComplete (r : ℕ) (A : Set ℕ) : Prop :=
  ∀ color : A → Fin r, ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    IsMonochromaticSum A color n

end Erdos55

namespace Erdos55

noncomputable def countUpTo (A : Set ℕ) (N : ℕ) : ℕ :=
  by
    classical
    exact ((Finset.Icc 1 N).filter (fun a ↦ a ∈ A)).card

end Erdos55

namespace Erdos55

def CFPUpperBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 2 ≤ r →
    ∃ A : PositiveNatSet, RamseyComplete r A ∧
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (countUpTo A N : ℝ) ≤ C * (r : ℝ) * Real.log (N : ℝ) ^ 2

end Erdos55

namespace Erdos55

def CFPLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ, 2 ≤ r → ∀ A : PositiveNatSet,
    (∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (countUpTo A N : ℝ) ≤ c * (r : ℝ) * Real.log (N : ℝ) ^ 2) →
    ¬ RamseyComplete r A

end Erdos55

namespace Erdos55

def ConlonFoxPhamResolution : Prop :=
  CFPUpperBound ∧ CFPLowerBound

end Erdos55

namespace Erdos55

theorem erdos_55 : ConlonFoxPhamResolution := by
  sorry

end Erdos55

end
