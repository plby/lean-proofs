/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.LeafObstructionEndgame
import ErdosProblems.Erdos570.EvenLeafCycle

/-!
# Closing an even cycle from repeated leaf obstructions

For an even cycle no extra endpoint edge is needed.  If `h` obstruction
parents have `h` common unused red neighbors, the two indexed sets form a
red `K_(h,h)`, and hence a red `C_(2h)`.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

theorem leafObstructionFamily_contains_even_cycle
    {W : Type*} [Fintype W] [DecidableEq W]
    {C : SimpleGraph W} {S T : Finset W} {q g h : ℕ}
    (hh : 2 ≤ h) (F : LeafObstructionFamily C S T q g h)
    (hcommon : h ≤ (commonPart F.unused T).card) :
    SimpleGraph.cycleGraph (2 * h) ⊑ C := by
  classical
  let A : Fin h → Finset W := fun _ ↦ commonPart F.unused T
  have hA : ∀ i, h ≤ (A i).card := by
    intro i
    simpa [A] using hcommon
  obtain ⟨w, hwinj, hwmem⟩ := exists_injective_mem_of_card_ge A hA
  have hwcommon (j : Fin h) : w j ∈ commonPart F.unused T := by
    simpa [A] using hwmem j
  have hdisj : ∀ i j, F.parent i ≠ w j := by
    intro i j hij
    have hred : C.Adj (F.parent i) (w j) :=
      F.red_neighborhood i (w j)
        (commonPart_subset F.unused T i (hwcommon j))
    exact hred.ne hij
  apply cycleGraph_even_isContained_of_complete_cross hh F.parent w
    F.parent_injective hwinj hdisj
  intro i j
  exact F.red_neighborhood i (w j)
    (commonPart_subset F.unused T i (hwcommon j))

end Erdos570
