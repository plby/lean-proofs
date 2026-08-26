import ErdosProblems.Erdos593.TripleSystem.TriangleHostRamsey
import ErdosProblems.Erdos593.TripleSystem.ObligatoryDisjointUnion

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A chromatic-cardinal consequence of the triangle-host Ramsey interface

This module converts the exact natural-colour Ramsey interface into the
strict cardinal lower bound required by the later obstruction argument.  It
is conditional on `PairRamseyTriangle`; it does not establish an
Erdős--Rado partition theorem.
-/

namespace Erdos593

open scoped Cardinal

universe u

namespace TripleSystem
namespace TriangleHost

/-- Under the Ramsey interface, the triangle host has chromatic cardinal
strictly above `ℵ₀`. -/
theorem aleph0_lt_chromaticCardinal_of_pairRamseyTriangle
    (κ : Type u) [DecidableEq κ]
    (hRamsey : PairRamseyTriangle κ) :
    ℵ₀ < (system κ).chromaticCardinal := by
  by_contra hnot
  have hle : (system κ).chromaticCardinal ≤ ℵ₀ := le_of_not_gt hnot
  have hle' : (system κ).chromaticCardinal ≤ #(ULift.{u} ℕ) := by
    simpa using! hle
  obtain ⟨c, hc⟩ :=
    ((system κ).chromaticCardinal_le_mk_iff (C := ULift.{u} ℕ)).mp hle'
  let d : Pair κ → ℕ := fun p ↦ (c p).down
  apply not_isProperColoring_nat_of_pairRamseyTriangle κ hRamsey d
  intro e
  rcases hc e with ⟨x, hx, y, hy, hxy⟩
  refine ⟨x, hx, y, hy, ?_⟩
  intro hdown
  apply hxy
  exact ULift.ext _ _ hdown

end TriangleHost
end TripleSystem
end Erdos593
