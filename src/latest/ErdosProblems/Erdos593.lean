import ErdosProblems.Erdos593.Proof

/-!
Lean version: 4.33.0 (ported from 4.32.0).
Formalization: Samuil Petkov, GPT-5.6 Pro, and Aristotle.
Eric Li's earlier proof architecture is credited in Erdos593/PROVENANCE.md.
See Erdos593/README.md and LICENSE_SCOPE.md for source and licensing details.
-/

namespace Erdos593

universe u

/-- The complete intrinsic classification after deleting isolated vertices. -/
theorem erdos_593 {V E : Type u} (F : TripleSystem V E) [Fintype V] [Fintype E] :
    F.IsObligatory ↔
      F.isolatedReduction.Linear ∧
      F.isolatedReduction.BridgeAtEveryEdge ∧
      F.isolatedReduction.EvenBergeCycles :=
  F.isObligatory_iff_isolatedReduction_intrinsic

end Erdos593

#print axioms Erdos593.erdos_593
