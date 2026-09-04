/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.AHTPairBridge
import ErdosProblems.Erdos916.AHTSourceLemma64
import ErdosProblems.Erdos916.AHTSection7TwoSeparation
import ErdosProblems.Erdos916.AHTUniverse

/-!
# Final bridge from AHT Theorem 6.6 to the dense graph theorem

This file records the short, reusable part of the final assembly.  The
source-level theorem supplies two disjoint degree-three false-twin pairs in
every separation-three-connected almost-wheel-free graph.  Section 7 turns
that output into the pointed vertex-two-connected theorem, the component
reduction gives one degree-three false-twin pair in every wheel-free graph of
minimum degree three, and `AHTUniverse` transports the universe-zero result
to arbitrary finite universes.
-/

namespace Erdos916

open _root_.SimpleGraph

/-- The source conclusion of AHT Theorem 6.6 implies the universe-zero
minimum-degree false-twin statement used by the extremal circuit assembly. -/
theorem degreeThreeFalseTwinPrinciple0_of_ahtTheorem66
    (h66 :
      ∀ (W : Type) [Fintype W] [DecidableEq W]
        (H : SimpleGraph W) [DecidableRel H.Adj],
        IsThreeConnected H → AlmostWheelFree H →
          Nonempty (TwoDisjointDegreeThreeFalseTwinPairs H)) :
    DegreeThreeFalseTwinPrinciple0 := by
  let hthreeCore : ThreeConnectedAlmostWheelFreeFalseTwinPrinciple := by
    intro W _ _ H _ hthree halmost
    obtain ⟨T⟩ := h66 W H
      (ahtDoublePinReplacement.isThreeConnected_of_vertexThreeConnected hthree)
      halmost
    exact ⟨T.toConnectivityPairs⟩
  have htwoCore : VertexTwoConnectedFalseTwinPrinciple :=
    AHTSection7TwoSeparation.vertexTwoConnectedFalseTwinPrinciple_of_threeConnected
      hthreeCore
  intro W _ _ H _ hcard hdegree hnoWheel
  let : Nonempty W := Fintype.card_pos_iff.mp (by omega)
  exact falseTwins_of_vertexTwoConnected htwoCore H hdegree hnoWheel

universe u

/-- The source-level AHT theorem implies the universe-polymorphic dense
graph conclusion.  This keeps the public Erdős theorem independent of the
universe-zero implementation details of the Watkins--Mesner machinery. -/
theorem erdos_916_of_ahtTheorem66
    (h66 :
      ∀ (W : Type) [Fintype W] [DecidableEq W]
        (H : SimpleGraph W) [DecidableRel H.Adj],
        IsThreeConnected H → AlmostWheelFree H →
          Nonempty (TwoDisjointDegreeThreeFalseTwinPairs H))
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : 4 ≤ Fintype.card V)
    (hedges : G.edgeFinset.card = 2 * Fintype.card V - 2) :
    HasWheelWitness G := by
  exact erdos_916_of_falseTwinPrinciple
    (degreeThreeFalseTwinPrinciple_of_typeZero
      (degreeThreeFalseTwinPrinciple0_of_ahtTheorem66 h66))
    G hcard hedges

end Erdos916
