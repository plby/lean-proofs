import ErdosProblems.Erdos538.ExplicitLinearBaseline
import ErdosProblems.Erdos538.UpperAsymptotic

/- Ported from Lean 4.31.0 to 4.33.0; imports, namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos538

/-- Increasing the allowed representation cap preserves admissibility. -/
theorem Admissible.mono_cap {r s N : ℕ} {A : Finset ℕ}
    (hA : Admissible r N A) (hrs : r ≤ s) : Admissible s N A := by
  refine ⟨hA.1, ?_⟩
  intro m
  exact (hA.2 m).trans hrs

/-- The nonnegative-rational reciprocal mass used in the lower construction is
exactly the real cast of the problem statement's rational reciprocal mass. -/
theorem coe_reciprocalMassNN_eq_reciprocalMass (A : Finset ℕ) :
    (reciprocalMassNN A : ℝ) = (reciprocalMass A : ℝ) := by
  unfold reciprocalMassNN reciprocalMass
  push_cast
  rfl

/-- Final faithful matching-order theorem for Erdős 538.  The first conjunct is
an explicit upper bound for every admissible family; the second gives matching
cap-two witnesses (hence witnesses for every `r≥2`) with only one iterated-log
factor. -/
theorem erdos538_matching_order
    (r N : ℕ) (hr : 2 ≤ r) (hN : 2 ≤ N) :
    (∀ A : Finset ℕ, Admissible r N A →
      Real.log (Real.log (N + 1)) * (reciprocalMass A : ℝ) ≤
        2 * r * (1 + Real.log (N * N))) ∧
    (∃ A : Finset ℕ,
      Admissible r N A ∧
      Real.log (N + 1) ≤
        4 + (8192 * (Nat.log 2 (Nat.log 2 N) + 1) : ℕ) *
          (reciprocalMass A : ℝ)) := by
  constructor
  · intro A hA
    exact admissible_explicit_log_upper hN hA
  · obtain ⟨A, hA, hmass⟩ :=
      exists_admissible_explicit_linear_log_baseline N
    refine ⟨A, hA.mono_cap hr, ?_⟩
    rw [← coe_reciprocalMassNN_eq_reciprocalMass]
    exact hmass

end Erdos538
