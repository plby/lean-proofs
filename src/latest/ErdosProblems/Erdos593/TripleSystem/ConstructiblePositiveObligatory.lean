import ErdosProblems.Erdos593.TripleSystem.CompleteBipartiteAtomObligatory
import ErdosProblems.Erdos593.TripleSystem.BridgeBlockRunningIntersection
import ErdosProblems.Erdos593.TripleSystem.ObligatoryConstructible

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Obligatory constructible triple systems

The all-parameter balanced complete-bipartite expansion atom theorem closes
the finite constructive closure argument: every constructible triple system
is obligatory.
-/

namespace Erdos593

universe u

namespace TripleSystem

/-- Every finite constructible triple system is obligatory. -/
theorem Constructible.isObligatory
    {V E : Type u} {F : TripleSystem V E} (hF : Constructible F) :
    F.IsObligatory := by
  apply hF.isObligatory_of_positive_completeBipartiteNN
  intro n _
  simpa only [completeBipartiteExpansionAtom] using!
    (completeBipartiteExpansionAtom_isObligatory.{u} n)

/-- A finite triple system whose isolated reduction is intrinsic is
obligatory. -/
theorem intrinsic_isolatedReduction_isObligatory
    {V E : Type u} (F : TripleSystem V E) [Finite V] [Finite E]
    (hF : F.isolatedReduction.Intrinsic) : F.IsObligatory := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let : Fintype E := Fintype.ofFinite E
  let : DecidableEq V := Classical.decEq V
  let : DecidableEq E := Classical.decEq E
  apply IsObligatory.of_isolatedReduction
  apply Constructible.isObligatory
  exact (BridgeBlock.isolatedReduction_constructible_iff_intrinsic F).mpr hF

end TripleSystem

end Erdos593
