import ErdosProblems.Erdos593.Graph.ShiftGraphOddGirth
import ErdosProblems.Erdos593.TripleSystem.SequenceLiftEmbeddedSourceIntrinsic

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Shift-graph odd-Berge obstruction

This file packages the odd-girth estimates for shift graphs with the generic
sequence-lift obstruction.  Together with `ShiftGraphChromatic`, it supplies
both host properties used by the avoidance argument: no countable colouring
and no sufficiently short odd closed walk.
-/

namespace Erdos593

universe u

namespace SequenceLift

variable {κ : Type u} [LinearOrder κ]
variable {X I : Type u} {F : TripleSystem X I}

/-- A shift graph with no countable colouring and odd-girth bound larger than
the finite Levi-edge bound witnesses that a finite linear source with an odd
Berge cycle in its isolated reduction is not obligatory. -/
theorem not_isObligatory_of_linear_of_not_isolatedReduction_evenBergeCycles_shiftGraph
    {r : ℕ}
    [Fintype I] [Fintype F.isolatedReduction.levi.edgeSet]
    (hcolor : ¬ Nonempty ((ShiftGraph.graph κ r).Coloring ℕ))
    (hgirth : F.isolatedReduction.levi.edgeFinset.card < 2 * r + 1)
    (hlinear : F.Linear)
    (hno : ¬ F.isolatedReduction.EvenBergeCycles) :
    ¬ F.IsObligatory := by
  exact not_isObligatory_of_linear_of_not_isolatedReduction_evenBergeCycles_of_host
    (G := ShiftGraph.graph κ r) hcolor hlinear hno
    (ShiftGraph.no_odd_closedWalk_up_to κ hgirth)

/-- A convenient specialization of
`not_isObligatory_of_linear_of_not_isolatedReduction_evenBergeCycles_shiftGraph`
where the shift length is chosen from the finite Levi-edge bound, making the
odd-girth inequality automatic. -/
theorem not_isObligatory_of_linear_of_not_isolatedReduction_evenBergeCycles_shiftGraph_succCard
    [Fintype I] [Fintype F.isolatedReduction.levi.edgeSet]
    (hcolor :
      ¬ Nonempty
        ((ShiftGraph.graph κ (F.isolatedReduction.levi.edgeFinset.card + 1)).Coloring ℕ))
    (hlinear : F.Linear)
    (hno : ¬ F.isolatedReduction.EvenBergeCycles) :
    ¬ F.IsObligatory := by
  exact not_isObligatory_of_linear_of_not_isolatedReduction_evenBergeCycles_shiftGraph
    (κ := κ) (F := F)
    hcolor (by omega) hlinear hno

end SequenceLift

end Erdos593
