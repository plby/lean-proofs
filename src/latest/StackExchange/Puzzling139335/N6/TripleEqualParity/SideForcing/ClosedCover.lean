import StackExchange.Puzzling139335.JordanRegion
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Closed tails of a side in a finite closed cover

This lemma uses the actual covering pieces and their closedness. It does
not require a straight side or any assumption about convex hulls.
-/

open Set

namespace Puzzling139335.N6.TripleEqualParity

/-- A closed piece owns the closed tail of a continuous side whenever all
other pieces meet that side only at parameters below the cutoff. -/
theorem closed_piece_owns_side_tail (d : SquareDissection) (j : Fin 4)
    (f : ℝ → Plane) (hf : Continuous f) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hsquare : ∀ y ∈ Icc (0 : ℝ) 1, f y ∈ unitSquare)
    (hother : ∀ i : Fin 4, i ≠ j →
      ∀ y ∈ Icc (0 : ℝ) 1, f y ∈ d.piece i → y ≤ a) :
    ∀ y ∈ Icc a 1, f y ∈ d.piece j := by
  have htail : Ioc a 1 ⊆ f ⁻¹' d.piece j := by
    intro y hy
    change f y ∈ d.piece j
    have hy01 : y ∈ Icc (0 : ℝ) 1 := ⟨ha0.trans hy.1.le, hy.2⟩
    obtain ⟨i, hi⟩ := d.exists_piece_mem (hsquare y hy01)
    by_cases hij : i = j
    · simpa only [hij] using hi
    · exact False.elim (not_le_of_gt hy.1 (hother i hij y hy01 hi))
  have hclosed : IsClosed (f ⁻¹' d.piece j) := (d.jordan j).isClosed.preimage hf
  have hclosure : closure (Ioc a 1) ⊆ f ⁻¹' d.piece j :=
    hclosed.closure_subset_iff.mpr htail
  rw [closure_Ioc ha1.ne] at hclosure
  exact fun y hy => hclosure hy

end Puzzling139335.N6.TripleEqualParity
