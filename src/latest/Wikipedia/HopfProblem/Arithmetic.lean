import Mathlib.Tactic

/-!
# The twisting arithmetic in `tex/s6.tex`, §7

The integer `twistOrder` is the expression used in Theorems 7.17 and 7.22.
These arithmetic theorems do not identify it with a fundamental group order;
that identification requires the geometric and topological construction.

Remark 7.28, page 63, omits an existential quantifier over the cusp twist.
`remark728_as_written_false` refutes the literal equivalence, and
`exists_unit_twist_iff` proves the version with that quantifier restored.
-/

namespace Wikipedia.HopfProblem

/-- The integer `p` of Theorem 7.17. -/
def twistOrder (ℓ₀ ℓ₁ ℓ₂ : ℤ) : ℤ := 12 * ℓ₀ - 4 * ℓ₁ - 3 * ℓ₂

/-- The admissibility conditions, written as integer congruences. -/
def AdmissibleTwists (ℓ₁ ℓ₂ : ℤ) : Prop := ℓ₁ % 3 ≠ 0 ∧ ℓ₂ % 2 = 1

/-- The pair of residue classes listed in Remark 7.28. -/
def UnitTwistResidues (ℓ₁ ℓ₂ : ℤ) : Prop :=
  (ℓ₁ % 3 = 1 ∧ ℓ₂ % 4 = 3) ∨ (ℓ₁ % 3 = 2 ∧ ℓ₂ % 4 = 1)

theorem main_twist_value : twistOrder 0 1 (-1) = -1 := by decide
theorem comparison_twist_value : twistOrder 0 1 1 = -7 := by decide

theorem twistOrder_shift (ℓ₀ ℓ₁ ℓ₂ k : ℤ) :
    twistOrder (ℓ₀ + k) ℓ₁ ℓ₂ = twistOrder ℓ₀ ℓ₁ ℓ₂ + 12 * k := by
  unfold twistOrder
  ring

theorem admissible_twistOrder_ne_zero (ℓ₀ ℓ₁ ℓ₂ : ℤ)
    (h : AdmissibleTwists ℓ₁ ℓ₂) : twistOrder ℓ₀ ℓ₁ ℓ₂ ≠ 0 := by
  unfold AdmissibleTwists at h
  unfold twistOrder
  omega

/-- A counterexample with admissible elliptic twists and the tautological
cusp twist: the listed residue pair is `(1, 3)`, but `p = -13`. -/
theorem remark728_counterexample :
    AdmissibleTwists 1 3 ∧ UnitTwistResidues 1 3 ∧
      twistOrder 0 1 3 = -13 ∧ |twistOrder 0 1 3| ≠ 1 := by
  norm_num [AdmissibleTwists, UnitTwistResidues, twistOrder]

/-- The same defect occurs with the paper's chosen elliptic twists unchanged,
by changing only the freely selectable cusp twist. -/
theorem remark728_cusp_counterexample :
    AdmissibleTwists 1 (-1) ∧ UnitTwistResidues 1 (-1) ∧
      twistOrder 1 1 (-1) = 11 ∧ |twistOrder 1 1 (-1)| ≠ 1 := by
  norm_num [AdmissibleTwists, UnitTwistResidues, twistOrder]

/-- The literal fixed-twist equivalence in Remark 7.28 is false. -/
theorem remark728_as_written_false :
    ¬ ∀ ℓ₀ ℓ₁ ℓ₂ : ℤ, AdmissibleTwists ℓ₁ ℓ₂ →
      (|twistOrder ℓ₀ ℓ₁ ℓ₂| = 1 ↔ UnitTwistResidues ℓ₁ ℓ₂) := by
  intro h
  have hbad := h 0 1 3 remark728_counterexample.1
  exact remark728_counterexample.2.2.2
    (hbad.mpr remark728_counterexample.2.1)

/-- The corrected arithmetic criterion: these residues characterize the
*existence* of a cusp twist giving `|p| = 1`, not every choice of cusp twist. -/
theorem exists_unit_twist_iff (ℓ₁ ℓ₂ : ℤ) :
    (∃ ℓ₀ : ℤ, |twistOrder ℓ₀ ℓ₁ ℓ₂| = 1) ↔ UnitTwistResidues ℓ₁ ℓ₂ := by
  constructor
  · rintro ⟨ℓ₀, h⟩
    rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)] at h
    unfold twistOrder at h
    unfold UnitTwistResidues
    omega
  · intro h
    rcases h with h | h
    · refine ⟨(4 * ℓ₁ + 3 * ℓ₂ - 1) / 12, ?_⟩
      rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)]
      unfold twistOrder
      omega
    · refine ⟨(4 * ℓ₁ + 3 * ℓ₂ + 1) / 12, ?_⟩
      rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)]
      unfold twistOrder
      omega

end Wikipedia.HopfProblem
