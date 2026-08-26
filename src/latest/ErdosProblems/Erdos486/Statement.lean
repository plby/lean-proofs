import Mathlib

/- Ported to Lean/Mathlib 4.33.0; see README.md for source and modifications. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Erdős Problem 486: exact statement

The activation condition is strict: a modulus `n` constrains `m` only when
`n < m`.  Keeping `A` explicit makes the quantifiers match the original
problem verbatim.
-/

open Filter Set

namespace Erdos486

/-- The positive integers surviving the delayed congruence system `(A, X)`.
The subtype index says that residue sets are supplied exactly for moduli in `A`.
-/
def survivors (A : Set ℕ) (X : (n : A) → Set (ZMod (n : ℕ))) : Set ℕ :=
  {m | 0 < m ∧ ∀ n : A, (n : ℕ) < m → (m : ZMod (n : ℕ)) ∉ X n}

/-- The logarithmic counting sum below a real cutoff. -/
noncomputable def logSum (B : Set ℕ) (x : ℝ) : ℝ :=
  by
    classical
    exact ∑ m ∈ Finset.range ⌈x⌉₊,
      if m ∈ B ∧ (m : ℝ) < x then (m : ℝ)⁻¹ else 0

/-- The normalized logarithmic average used in Erdős Problem 486. -/
noncomputable def logAverage (B : Set ℕ) (x : ℝ) : ℝ :=
  logSum B x / Real.log x

/-- A set has logarithmic density `d` in the exact normalization of the problem. -/
def HasLogDensity (B : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (logAverage B) atTop (nhds d)

/-- The original yes/no assertion in Erdős Problem 486. -/
def Erdos486Assertion : Prop :=
  ∀ (A : Set ℕ) (X : (n : A) → Set (ZMod (n : ℕ))), 0 ∉ A →
    ∃ d : ℝ, HasLogDensity (survivors A X) d

/-- The quantitative strengthening claimed in the accompanying manuscript. -/
def QuantitativeCounterexample : Prop :=
  ∃ (A : Set ℕ), A.Infinite ∧ 0 ∉ A ∧
    ∃ X : (n : A) → Set (ZMod (n : ℕ)),
      let B := survivors A X
      (¬ ∃ d : ℝ, HasLogDensity B d) ∧
      liminf (logAverage B) atTop ≤ (177 : ℝ) / 200 ∧
      (49 : ℝ) / 50 ≤ limsup (logAverage B) atTop

theorem quantitativeCounterexample_not_assertion :
    QuantitativeCounterexample → ¬Erdos486Assertion := by
  rintro ⟨A, _, hA, X, hnone, _, _⟩ hall
  exact hnone (hall A X hA)

end Erdos486
