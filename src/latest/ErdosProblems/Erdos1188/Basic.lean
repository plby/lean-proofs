import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; module names and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Minimal distinct covering systems

This file pins down the objects counted in Erdős Problem 1188.  A congruence
class is stored canonically as `(modulus, residue)` with `2 ≤ modulus` and
`residue < modulus`.  Thus two pairs represent the same class exactly when they
are equal.

The phrase "estimate `F(x)`" in the source problem does not prescribe one
particular asymptotic assertion.  `coveringCount` is the faithful formal object;
all proposed upper or lower estimates must be theorems about this function.
-/

namespace Erdos1188

/-- A canonical congruence class, represented by its modulus and least
nonnegative residue.  Validity is imposed separately by `ValidClass`. -/
abbrev CongruenceClass := ℕ × ℕ

/-- The pair `(n,a)` canonically represents `a (mod n)`, with the problem's
condition `1 < n`. -/
def ValidClass (c : CongruenceClass) : Prop := 2 ≤ c.1 ∧ c.2 < c.1

/-- An integer belongs to the congruence class `(n,a)`. -/
def Satisfies (z : ℤ) (c : CongruenceClass) : Prop :=
  z % (c.1 : ℤ) = (c.2 : ℤ)

/-- Every integer lies in at least one member of `S`. -/
def Covers (S : Finset CongruenceClass) : Prop :=
  ∀ z : ℤ, ∃ c ∈ S, Satisfies z c

/-- No two classes in `S` have the same modulus. -/
def HasDistinctModuli (S : Finset CongruenceClass) : Prop :=
  ∀ ⦃c₁⦄, c₁ ∈ S → ∀ ⦃c₂⦄, c₂ ∈ S → c₁.1 = c₂.1 → c₁ = c₂

/-- A direct transcription of a minimal distinct covering system: all classes
are canonical and have modulus greater than one, the moduli are distinct, the
classes cover every integer, and no proper subfamily covers every integer. -/
def IsMinimalDistinctCoveringSystem (S : Finset CongruenceClass) : Prop :=
  (∀ c ∈ S, ValidClass c) ∧
  HasDistinctModuli S ∧
  Covers S ∧
  ∀ T : Finset CongruenceClass, T ⊂ S → ¬ Covers T

/-- All canonical congruence classes whose moduli lie in `[2,x]`. -/
def ClassesUpTo (x : ℕ) : Finset CongruenceClass :=
  (Finset.Icc 2 x).biUnion fun n =>
    (Finset.range n).image fun a => (n, a)

/-- The finite collection of all minimal distinct covering systems with every
modulus at most `x`.  Classical decidability is used only to filter a finite
powerset by the mathematical covering predicate. -/
noncomputable def MinimalDistinctCoveringSystemsUpTo (x : ℕ) :
    Finset (Finset CongruenceClass) := by
  classical
  exact (ClassesUpTo x).powerset.filter IsMinimalDistinctCoveringSystem

/-- The counting function `F(x)` in Erdős Problem 1188. -/
noncomputable def coveringCount (x : ℕ) : ℕ :=
  (MinimalDistinctCoveringSystemsUpTo x).card

/-- A proposed estimate can be stated without ambiguity as eventual pointwise
bounds on the real-valued coercion of `coveringCount`. -/
def IsAsymptoticEstimate (lower upper : ℕ → ℝ) : Prop :=
  (∀ᶠ x in Filter.atTop, lower x ≤ coveringCount x) ∧
  (∀ᶠ x in Filter.atTop, (coveringCount x : ℝ) ≤ upper x)

end Erdos1188
