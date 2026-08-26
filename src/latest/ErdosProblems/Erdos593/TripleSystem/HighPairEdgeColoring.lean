import ErdosProblems.Erdos593.TripleSystem.HighPairGraph
import ErdosProblems.Erdos593.TripleSystem.PredicateColoring

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The high-pair / low-pair edge partition

For a fixed codegree threshold, this module partitions the indexed edges of a
triple-system host according to whether they contain a high pair.  The
high-pair part is exactly the family induced by the high-pair graph, so any
countable colouring of that graph immediately gives a proper colouring of the
selected hyperedges.  The complementary low-pair family is kept as a
predicate on the original edge indices; this avoids changing the host vertex
type before the closure argument is applied.
-/

namespace Erdos593

universe u v w

namespace TripleSystem

variable {W : Type u} {D : Type v} (H : TripleSystem W D)

/-- The indexed host edges which contain an edge of the threshold-`t`
high-pair graph. -/
def highPairEdge (t : Nat) : D → Prop :=
  H.EdgeContainsGraphEdge (highPairGraph H t)

/-- The complementary indexed host edges: those containing no threshold-`t`
high pair. -/
def lowPairEdge (t : Nat) : D → Prop := fun e => ¬ H.highPairEdge t e

/-- Unfold the high-pair edge predicate into an explicit pair of incident
vertices. -/
theorem highPairEdge_iff {t : Nat} {e : D} :
    H.highPairEdge t e ↔
      ∃ x y : W, H.Inc x e ∧ H.Inc y e ∧ HighPair H t x y :=
  Iff.rfl

/-- An explicitly exhibited high pair inside an indexed edge puts that edge
in the high-pair family. -/
theorem highPairEdge_of_incident_highPair {t : Nat} {e : D} {x y : W}
    (hxe : H.Inc x e) (hye : H.Inc y e) (hxy : HighPair H t x y) :
    H.highPairEdge t e :=
  ⟨x, y, hxe, hye, hxy⟩

/-- Every high-pair edge supplies an explicitly incident high pair. -/
theorem exists_incident_highPair_of_highPairEdge {t : Nat} {e : D}
    (he : H.highPairEdge t e) :
    ∃ x y : W, H.Inc x e ∧ H.Inc y e ∧ HighPair H t x y :=
  he

/-- A low-pair edge has no high pair among any two of its incident vertices. -/
theorem not_highPair_of_lowPairEdge {t : Nat} {e : D} {x y : W}
    (he : H.lowPairEdge t e) (hxe : H.Inc x e) (hye : H.Inc y e) :
    ¬ HighPair H t x y := by
  intro hxy
  exact he (H.highPairEdge_of_incident_highPair hxe hye hxy)

/-- Conversely, an edge is low-pair precisely when none of its incident
pairs is high at the selected threshold. -/
theorem lowPairEdge_iff {t : Nat} {e : D} :
    H.lowPairEdge t e ↔
      ∀ x y : W, H.Inc x e → H.Inc y e → ¬ HighPair H t x y := by
  constructor
  · intro he x y hxe hye
    exact H.not_highPair_of_lowPairEdge he hxe hye
  · intro he hhigh
    rcases hhigh with ⟨x, y, hxe, hye, hxy⟩
    exact he x y hxe hye hxy

/-- The high-pair and low-pair predicates form an exhaustive partition of
the original host edge indices. -/
theorem highPairEdge_or_lowPairEdge (t : Nat) (e : D) :
    H.highPairEdge t e ∨ H.lowPairEdge t e := by
  exact Classical.em _

/-- The two parts of the high-pair/low-pair partition are disjoint. -/
theorem not_highPairEdge_and_lowPairEdge {t : Nat} {e : D} :
    ¬ (H.highPairEdge t e ∧ H.lowPairEdge t e) := by
  rintro ⟨hhigh, hlow⟩
  exact hlow hhigh

/-- Re-express membership in the high-pair family through failure of the
complementary low-pair predicate. -/
theorem highPairEdge_iff_not_lowPairEdge {t : Nat} {e : D} :
    H.highPairEdge t e ↔ ¬ H.lowPairEdge t e := by
  simp only [lowPairEdge]
  exact Classical.not_not.symm

/-- Re-express membership in the low-pair family through failure of the
high-pair predicate. -/
theorem lowPairEdge_iff_not_highPairEdge {t : Nat} {e : D} :
    H.lowPairEdge t e ↔ ¬ H.highPairEdge t e :=
  Iff.rfl

/-- A proper colouring of the high-pair graph is proper on every host edge
which contains a high pair. -/
theorem isProperColoringOn_highPairEdge {t : Nat} {C : Type w}
    (c : (highPairGraph H t).Coloring C) :
    H.IsProperColoringOn (H.highPairEdge t) (fun z => c z) := by
  simpa only [highPairEdge] using!
    H.isProperColoringOn_edgeContainsGraphEdge c

/-- A countable colouring of the high-pair graph colours the high-pair part
of the host edge partition. -/
theorem countablyColorableOn_highPairEdge {t : Nat}
    (hG : Erdos593.SimpleGraph.CountablyColorable (highPairGraph H t)) :
    H.CountablyColorableOn (H.highPairEdge t) := by
  simpa only [highPairEdge] using!
    H.countablyColorableOn_edgeContainsGraphEdge hG

end TripleSystem

end Erdos593
