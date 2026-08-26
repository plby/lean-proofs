import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseApex

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Canonical incidence in one sequence-lift edge

This local normal form identifies the three points incident with a lift edge:
the two endpoints of its canonical base letter at the canonical base node,
and its canonical apex. It makes no claim about other edges or fibres.
-/

namespace Erdos593

universe u

namespace SequenceLift

variable {V : Type u} (G : _root_.SimpleGraph V)

/-- A lift edge is incident exactly with the two base-letter points at its
canonical base node and with its canonical apex. -/
theorem inc_iff_baseNode_baseLetter_or_baseApex
    (e : Edge G) (p : Point G) :
    (system G).Inc p e ↔
      (p.1 = baseNode e ∧ p.2 ∈ (baseLetter e).1) ∨ p = baseApex e := by
  rcases exists_mkEdge_at_baseNode e with ⟨t, x, y, z, hxy, hext, he⟩
  rw [he, inc_mkEdge_iff, baseNode_mkEdge, baseLetter_mkEdge, baseApex_mkEdge]
  constructor
  · rintro (hp | hp | hp)
    · subst p
      left
      constructor
      · rfl
      · simp [edgeLetter]
    · subst p
      left
      constructor
      · rfl
      · simp [edgeLetter]
    · exact Or.inr hp
  · rintro (⟨hnode, hmem⟩ | hp)
    · change p.2 ∈ s(x, y) at hmem
      rcases Sym2.mem_iff.mp hmem with hx | hy
      · left
        exact Prod.ext hnode hx
      · right
        left
        exact Prod.ext hnode hy
    · exact Or.inr (Or.inr hp)

end SequenceLift
end Erdos593
