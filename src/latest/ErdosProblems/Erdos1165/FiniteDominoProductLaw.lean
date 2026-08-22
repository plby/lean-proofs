import Mathlib

/-!
# Coordinate-system-neutral finite domino product laws

The horizontal insertion development indexes product coordinates by
`ExternalDomino`.  The six HLOZ tilings have a different state-dependent
domino index.  This file records the finite product and distinguished-
marginal algebra for an arbitrary finite domino type.
-/

open scoped BigOperators

namespace Erdos1165.FiniteDominoProductLaw

noncomputable section

/-- A heterogeneous vector of truncated nonnegative-integer totals. -/
abbrev TruncatedTotals {Domino : Type*} (upper : Domino → ℕ) :=
  (b : Domino) → Fin (upper b)

/-- Unnormalized point mass of an independent heterogeneous vector. -/
noncomputable def jointMass {Domino : Type*} [Fintype Domino]
    [DecidableEq Domino]
    (pointMass : Domino → ℕ → ℝ) (upper : Domino → ℕ)
    (ell : TruncatedTotals upper) : ℝ :=
  ∏ b, pointMass b (ell b)

/-- One-coordinate truncated normalization. -/
noncomputable def coordinateMass {Domino : Type*} [Fintype Domino]
    [DecidableEq Domino]
    (pointMass : Domino → ℕ → ℝ) (upper : Domino → ℕ)
    (b : Domino) (ell : ℕ) : ℝ :=
  if ell < upper b then
    pointMass b ell / ∑ j : Fin (upper b), pointMass b j
  else 0

/-- Normalized joint point mass. -/
noncomputable def normalizedJointMass {Domino : Type*} [Fintype Domino]
    [DecidableEq Domino]
    (pointMass : Domino → ℕ → ℝ) (upper : Domino → ℕ)
    (ell : TruncatedTotals upper) : ℝ :=
  jointMass pointMass upper ell /
    ∑ z : TruncatedTotals upper, jointMass pointMass upper z

/-- The finite normalization is the product of the one-coordinate
normalizations. -/
theorem normalizedJointMass_eq_product
    {Domino : Type*} [Fintype Domino] [DecidableEq Domino]
    (pointMass : Domino → ℕ → ℝ) (upper : Domino → ℕ)
    (ell : TruncatedTotals upper) :
    normalizedJointMass pointMass upper ell =
      ∏ b, coordinateMass pointMass upper b (ell b) := by
  classical
  unfold normalizedJointMass jointMass coordinateMass
  have hden := Finset.prod_univ_sum
    (fun b : Domino ↦ (Finset.univ : Finset (Fin (upper b))))
    (fun b j ↦ pointMass b (j : ℕ))
  rw [Fintype.piFinset_univ] at hden
  rw [hden.symm, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro b _
  rw [if_pos (ell b).isLt]

/-- Probability of a predicate under the normalized finite product law. -/
noncomputable def screenMass {Domino : Type*} [Fintype Domino]
    [DecidableEq Domino]
    (pointMass : Domino → ℕ → ℝ) (upper : Domino → ℕ)
    (screen : TruncatedTotals upper → Prop) [DecidablePred screen] : ℝ :=
  ∑ ell : TruncatedTotals upper,
    if screen ell then normalizedJointMass pointMass upper ell else 0

theorem screenMass_eq_product
    {Domino : Type*} [Fintype Domino] [DecidableEq Domino]
    (pointMass : Domino → ℕ → ℝ) (upper : Domino → ℕ)
    (screen : TruncatedTotals upper → Prop) [DecidablePred screen] :
    screenMass pointMass upper screen =
      ∑ ell : TruncatedTotals upper,
        if screen ell then
          ∏ b, coordinateMass pointMass upper b (ell b)
        else 0 := by
  unfold screenMass
  apply Finset.sum_congr rfl
  intro ell _
  by_cases hell : screen ell <;>
    simp [hell, normalizedJointMass_eq_product]

/-- Arbitrary finite data carried only by distinguished domino coordinates
contribute a common factor to every away-total vector. -/
noncomputable def distinguishedAwayMass
    {Domino Delta : Type*} [Fintype Domino] [DecidableEq Domino]
    [Fintype Delta]
    (pointMass : Domino → ℕ → ℝ) (upper : Domino → ℕ)
    (distinguishedMass : Delta → ℝ) (ell : TruncatedTotals upper) : ℝ :=
  ∑ d, jointMass pointMass upper ell * distinguishedMass d

/-- Exact cancellation of the distinguished-coordinate marginal for an
arbitrary finite screen on the away totals. -/
theorem screenMass_mul_distinguishedBase
    {Domino Delta : Type*} [Fintype Domino] [DecidableEq Domino]
    [Fintype Delta]
    (pointMass : Domino → ℕ → ℝ) (upper : Domino → ℕ)
    (screen : TruncatedTotals upper → Prop) [DecidablePred screen]
    (distinguishedMass : Delta → ℝ)
    (htotal : (∑ ell : TruncatedTotals upper,
      jointMass pointMass upper ell) ≠ 0) :
    screenMass pointMass upper screen *
        (∑ ell : TruncatedTotals upper,
          distinguishedAwayMass pointMass upper distinguishedMass ell) =
      ∑ ell : TruncatedTotals upper,
        if screen ell then
          distinguishedAwayMass pointMass upper distinguishedMass ell else 0 := by
  classical
  let total := ∑ ell : TruncatedTotals upper,
    jointMass pointMass upper ell
  let selected := ∑ ell : TruncatedTotals upper,
    if screen ell then jointMass pointMass upper ell else 0
  let dist := ∑ d, distinguishedMass d
  have hproduct : screenMass pointMass upper screen = selected / total := by
    unfold screenMass normalizedJointMass selected total
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro ell _
    by_cases hell : screen ell <;> simp [hell]
  have hbase :
      (∑ ell : TruncatedTotals upper,
        distinguishedAwayMass pointMass upper distinguishedMass ell) =
        total * dist := by
    unfold distinguishedAwayMass total dist
    simp_rw [← Finset.mul_sum]
    rw [Finset.sum_mul]
  have hscreen :
      (∑ ell : TruncatedTotals upper,
        if screen ell then
          distinguishedAwayMass pointMass upper distinguishedMass ell else 0) =
        selected * dist := by
    unfold distinguishedAwayMass selected dist
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ell _
    by_cases hell : screen ell <;> simp [hell, Finset.mul_sum]
  rw [hproduct, hbase, hscreen]
  field_simp [total, htotal]

end

end Erdos1165.FiniteDominoProductLaw
