import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseNode

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Canonical normal forms for sequence-lift edges

The canonical base-node selector lets every lift edge be displayed using its
own selected base node.  At that node the edge has exactly its two graph-base
points; at every other node it has at most one point.
-/

namespace Erdos593

open scoped Cardinal Ordinal

universe u

namespace SequenceLift

variable {V : Type u} {G : _root_.SimpleGraph V}

/-- Every sequence-lift edge has a displayed representation whose source is
its canonical base node. -/
theorem exists_mkEdge_at_baseNode (e : Edge G) :
    ∃ (t : Node G) (x y z : V) (hxy : G.Adj x y)
      (hext : (baseNode e).ExtendsBy (edgeLetter hxy) t),
      e = mkEdge (baseNode e) t x y z hxy hext := by
  rcases e.2 with ⟨q, t, x, y, z, hxy, hext, hset⟩
  have he : e = mkEdge q t x y z hxy hext := by
    apply Subtype.ext
    simpa only [mkEdge] using! hset
  have hq : q = baseNode e := by
    apply basedAt_unique (e := e)
    · rw [he]
      exact mkEdge_basedAt
    · exact baseNode_basedAt e
  subst q
  exact ⟨t, x, y, z, hxy, hext, he⟩

/-- Pointwise form of the canonical-base-node characterization. -/
theorem eq_baseNode_iff_exists_distinct_incident
    (q : Node G) (e : Edge G) :
    q = baseNode e ↔
      ∃ x y : V, x ≠ y ∧
        (system G).Inc (q, x) e ∧ (system G).Inc (q, y) e := by
  simpa only [BasedAt] using! (basedAt_iff_baseNode_eq q e).symm

/-- Away from its canonical base node, a sequence-lift edge has at most one
incident point over any fixed node. -/
theorem point_eq_of_inc_of_ne_baseNode
    {q : Node G} {e : Edge G} {x y : V}
    (hq : q ≠ baseNode e)
    (hx : (system G).Inc (q, x) e)
    (hy : (system G).Inc (q, y) e) :
    x = y := by
  by_contra hxy
  apply hq
  exact (basedAt_iff_baseNode_eq q e).mp ⟨x, y, hxy, hx, hy⟩

/-- The fibre of a sequence-lift edge at its canonical base node is exactly
the pair of endpoints of one graph edge. -/
theorem exists_basePair_at_baseNode (e : Edge G) :
    ∃ x y : V, G.Adj x y ∧
      ∀ w : V,
        (system G).Inc (baseNode e, w) e ↔ w = x ∨ w = y := by
  rcases e.2 with ⟨q, t, x, y, z, hxy, hext, hset⟩
  have he : e = mkEdge q t x y z hxy hext := by
    apply Subtype.ext
    simpa only [mkEdge] using! hset
  rw [he]
  refine ⟨x, y, hxy, ?_⟩
  intro w
  rw [baseNode_mkEdge, inc_mkEdge_iff]
  constructor
  · intro hw
    rcases hw with hw | hw
    · exact Or.inl (congrArg Prod.snd hw)
    rcases hw with hw | hw
    · exact Or.inr (congrArg Prod.snd hw)
    · exact (Node.ne_of_extendsBy hext (congrArg Prod.fst hw)).elim
  · intro hw
    rcases hw with hw | hw
    · subst w
      exact Or.inl rfl
    · subst w
      exact Or.inr (Or.inl rfl)

end SequenceLift
end Erdos593
