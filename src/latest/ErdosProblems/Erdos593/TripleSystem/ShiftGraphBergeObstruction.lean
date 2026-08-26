import ErdosProblems.Erdos593.Graph.ShiftGraphHost
import ErdosProblems.Erdos593.TripleSystem.SequenceLiftEmbeddedSourceEndpoints
import ErdosProblems.Erdos593.TripleSystem.SequenceLiftChromatic
import ErdosProblems.Erdos593.TripleSystem.FiniteLiftGeneratedBergeCycleTrace

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Odd Berge-cycle obstruction from shift-graph hosts
-/

namespace Erdos593

universe u

namespace SequenceLift

variable {X I : Type u} {F : TripleSystem X I}

/-- A specified odd Berge cycle in the isolated reduction prevents embedding
into the corresponding shift-graph sequence lift. -/
theorem not_nonempty_embedding_shiftHost_of_oddBergeCycle
    [Fintype I] (hlinear : F.Linear)
    {z : F.NonIsolatedPoint ⊕ I}
    (c : F.isolatedReduction.levi.Walk z z) (hc : c.IsCycle)
    (hodd : ¬ 4 ∣ c.length) :
    ¬ Nonempty (F.Embedding (system (ShiftGraph.hostGraph.{u} c.length))) := by
  rintro ⟨f⟩
  have hgenerated :=
    isolatedReduction_finiteLiftGenerated_of_linear_of_embedding f hlinear
  have htrace := TripleSystem.FiniteLiftGenerated.bergeCycleTraceTo
    (ShiftGraph.hostGraph.{u} c.length) hgenerated
  have heven := TripleSystem.BergeCycleTraceTo.evenBergeCycles_up_to
    (ShiftGraph.hostGraph.{u} c.length) htrace c.length
    (ShiftGraph.hostGraph_no_odd_closedWalk_up_to c.length)
    c hc (by omega)
  exact hodd heven

/-- A finite linear triple system whose isolated reduction has an odd Berge
cycle is not obligatory. -/
theorem not_isObligatory_of_linear_of_not_isolatedReduction_evenBergeCycles_shiftHost
    (F : TripleSystem X I) [Fintype I]
    (hlinear : F.Linear)
    (hno : ¬ F.isolatedReduction.EvenBergeCycles) :
    ¬ F.IsObligatory := by
  classical
  rw [TripleSystem.EvenBergeCycles] at hno
  push Not at hno
  obtain ⟨z, c, hc, hodd⟩ := hno
  intro hF
  have hembedding := hF _ _
    (system (ShiftGraph.hostGraph.{u} c.length))
    (aleph0_lt_chromaticCardinal
      (ShiftGraph.hostGraph_not_nonempty_coloring_nat c.length))
  exact not_nonempty_embedding_shiftHost_of_oddBergeCycle hlinear c hc hodd
    hembedding

end SequenceLift

end Erdos593
