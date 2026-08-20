/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.CoreRigidity

/-!
# The precise boundary of the direct `(2,3)`-circuit formulation

The density reduction used for Erdős Problem 916 produces circuits on at
least four vertices.  That order hypothesis cannot be dropped from a direct
circuit theorem: on a singleton vertex type the empty graph satisfies the
literal definition of `Is23Circuit`, while it has no cycle at all.

This file records that counterexample inside Lean.  It prevents the final
theorem from accidentally being stated as the false bare implication
`Is23Circuit G → HasWheelWitness G`; the correct circuit statement also has
the hypothesis `4 ≤ Fintype.card V`.
-/

namespace Erdos916

open SimpleGraph

attribute [local instance] Classical.propDecidable

/-- The empty graph on one vertex satisfies the literal `(2,3)`-circuit
definition.  The global count is `0 + 2 = 2 * 1`, and no finset of the
singleton carrier has the two vertices required by the sparsity clause. -/
theorem singleton_bottom_is23Circuit :
    @Is23Circuit PUnit inferInstance (⊥ : SimpleGraph PUnit)
      (Classical.decRel (⊥ : SimpleGraph PUnit).Adj) := by
  constructor
  · simp [Has23CircuitCount]
  · intro S hS
    have hle : S.card ≤ 1 := by
      simpa using S.card_le_univ
    omega

/-- The empty graph has no wheel witness (indeed, it has no nonempty walk). -/
theorem singleton_bottom_not_hasWheelWitness :
    ¬@HasWheelWitness PUnit inferInstance inferInstance
      (⊥ : SimpleGraph PUnit)
      (Classical.decRel (⊥ : SimpleGraph PUnit).Adj) := by
  rintro ⟨a, p, x, hp, -⟩
  cases p with
  | nil => exact hp.not_nil Walk.nil_nil
  | cons hadj _ => exact hadj

/-- Consequently the bare direct circuit implication requested without an
order hypothesis is false. -/
theorem not_forall_is23Circuit_imp_hasWheelWitness :
    ¬(∀ (G : SimpleGraph PUnit) [DecidableRel G.Adj],
        Is23Circuit G → HasWheelWitness G) := by
  intro h
  let d : DecidableRel (⊥ : SimpleGraph PUnit).Adj :=
    Classical.decRel _
  exact singleton_bottom_not_hasWheelWitness
    (@h (⊥ : SimpleGraph PUnit) d singleton_bottom_is23Circuit)

end Erdos916

#print axioms Erdos916.not_forall_is23Circuit_imp_hasWheelWitness
