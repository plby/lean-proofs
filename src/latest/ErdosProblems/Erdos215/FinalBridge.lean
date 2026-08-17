import ErdosProblems.Erdos215.RationalLattice

/-!
# The final geometric bridge for Erdős Problem 215

The global construction is naturally phrased as hitting every rational
equivalence class of oriented lattices.  This file converts that conclusion
to the inverse-motion formulation used by the literal problem statement.
-/

namespace Erdos215

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- Hitting every rational class of oriented lattice frames entails hitting
the inverse image of the integer lattice under every direct rigid motion. -/
theorem hitsEveryLattice_of_hitsEveryRationalClass {S : Set Point}
    (h : ∀ L K : OrientedFrame, K.RationallyEquivalent L →
      ∃ p : Point, p ∈ S ∧ K.IsLatticePoint p) :
    HitsEveryLattice S := by
  intro t c s hcs
  let L : OrientedFrame :=
    { origin := inverseMotion t c s 0
      c := c
      s := -s
      unit := by nlinarith }
  obtain ⟨p, hpS, hpL⟩ := h L L (OrientedFrame.rationallyEquivalent_refl L)
  rcases hpL with ⟨z, rfl⟩
  refine ⟨z, ?_⟩
  simpa only [L, OrientedFrame.fromCoords, inverseMotion, rotate_zero,
    zero_sub, rotate_neg, rotate_sub, rotate_add, sub_eq_add_neg, add_comm,
    add_zero] using hpS

end

end Erdos215
