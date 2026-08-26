import ErdosProblems.Erdos593.TripleSystem.SequenceLiftEmbeddedSourceEndpoints
import ErdosProblems.Erdos593.TripleSystem.ConstructiveForward
import ErdosProblems.Erdos593.TripleSystem.SequenceLiftChromatic

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos593

universe u

namespace SequenceLift

variable {V : Type u} {G : _root_.SimpleGraph V}
variable {X I : Type u} {F : TripleSystem X I}

/-- A finite linear source embedded in a sequence lift has an isolated
reduction with only even Berge cycles whenever the host graph has no odd
closed walk up to the finite Levi-edge bound of that isolated reduction. -/
theorem isolatedReduction_evenBergeCycles_of_linear_of_embedding
    [Fintype I] [Fintype F.isolatedReduction.levi.edgeSet]
    (f : F.Embedding (system G)) (hlinear : F.Linear)
    (hG : ∀ ⦃v : V⦄ (q : G.Walk v v),
      q.length ≤ F.isolatedReduction.levi.edgeFinset.card → ¬ Odd q.length) :
    F.isolatedReduction.EvenBergeCycles := by
  exact TripleSystem.BergeCycleTraceTo.evenBergeCycles_of_no_odd_closedWalk_up_to
    G F.isolatedReduction
    (isolatedReduction_bergeCycleTraceTo_of_linear_of_embedding f hlinear)
    hG

/-- A finite linear source whose isolated reduction has an odd Berge cycle
cannot embed in a sequence lift over a host graph with no sufficiently short
odd closed walk. -/
theorem not_nonempty_embedding_of_not_isolatedReduction_evenBergeCycles
    [Fintype I] [Fintype F.isolatedReduction.levi.edgeSet]
    (hlinear : F.Linear)
    (hno : ¬ F.isolatedReduction.EvenBergeCycles)
    (hG : ∀ ⦃v : V⦄ (q : G.Walk v v),
      q.length ≤ F.isolatedReduction.levi.edgeFinset.card → ¬ Odd q.length) :
    ¬ Nonempty (F.Embedding (system G)) := by
  rintro ⟨f⟩
  exact hno (isolatedReduction_evenBergeCycles_of_linear_of_embedding
    f hlinear hG)

/-- A finite linear source whose isolated reduction has an odd Berge cycle
is not obligatory whenever a host graph has no countable colouring and no odd
closed walk up to the finite Levi-edge bound.  The later shift-graph package
will instantiate these two host hypotheses simultaneously. -/
theorem not_isObligatory_of_linear_of_not_isolatedReduction_evenBergeCycles_of_host
    [Fintype I] [Fintype F.isolatedReduction.levi.edgeSet]
    (hGcolor : ¬ Nonempty (G.Coloring ℕ))
    (hlinear : F.Linear)
    (hno : ¬ F.isolatedReduction.EvenBergeCycles)
    (hGwalk : ∀ ⦃v : V⦄ (q : G.Walk v v),
      q.length ≤ F.isolatedReduction.levi.edgeFinset.card → ¬ Odd q.length) :
    ¬ F.IsObligatory := by
  classical
  intro hF
  exact not_nonempty_embedding_of_not_isolatedReduction_evenBergeCycles
    hlinear hno hGwalk
    (hF _ _ (system G) (aleph0_lt_chromaticCardinal hGcolor))

/-- A finite linear source embedded in a two-colourable sequence lift has an
intrinsic isolated reduction. -/
theorem isolatedReduction_intrinsic_of_linear_of_embedding
    [Fintype I]
    (f : F.Embedding (system G)) (hlinear : F.Linear)
    (hG : G.Colorable 2) :
    F.isolatedReduction.Intrinsic := by
  exact TripleSystem.Constructible.intrinsic
    (isolatedReduction_constructible_of_linear_of_embedding f hlinear hG)

end SequenceLift
end Erdos593
