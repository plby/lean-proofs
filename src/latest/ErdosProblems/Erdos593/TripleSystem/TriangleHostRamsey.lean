import ErdosProblems.Erdos593.TripleSystem.TriangleHostLinearity
import ErdosProblems.Erdos593.TripleSystem.Obligatory

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A Ramsey interface for the triangle host

This module isolates the exact Ramsey consequence needed to rule out a
natural-number proper colouring of `TriangleHost.system`.  It does not prove
the Ramsey hypothesis itself: that remains the separate Erdős--Rado/cardinal
layer of the classical positive-atom programme.
-/

namespace Erdos593

universe u

namespace TripleSystem
namespace TriangleHost

/-- Every natural-number colouring of pair-vertices has a triangle all of whose
pair-faces have one colour. -/
def PairRamseyTriangle (κ : Type u) [DecidableEq κ] : Prop :=
  ∀ c : Pair κ → ℕ, ∃ t : Triangle κ,
    ∀ p q : Pair κ, p.1 ⊆ t.1 → q.1 ⊆ t.1 → c p = c q

/-- Under `PairRamseyTriangle`, a natural-number colouring of the triangle
host cannot be proper. -/
theorem not_isProperColoring_nat_of_pairRamseyTriangle
    (κ : Type u) [DecidableEq κ]
    (hRamsey : PairRamseyTriangle κ) (c : Pair κ → ℕ) :
    ¬ (system κ).IsProperColoring c := by
  intro hc
  obtain ⟨t, ht⟩ := hRamsey c
  rcases hc t with ⟨p, hp, q, hq, hpq⟩
  exact hpq (ht p q hp hq)

/-- Under `PairRamseyTriangle`, the triangle host has no proper countable
colouring expressed with natural-number colours. -/
theorem no_natProperColoring_of_pairRamseyTriangle
    (κ : Type u) [DecidableEq κ]
    (hRamsey : PairRamseyTriangle κ) :
    ¬ ∃ c : Pair κ → ℕ, (system κ).IsProperColoring c := by
  rintro ⟨c, hc⟩
  exact not_isProperColoring_nat_of_pairRamseyTriangle κ hRamsey c hc

end TriangleHost
end TripleSystem
end Erdos593
