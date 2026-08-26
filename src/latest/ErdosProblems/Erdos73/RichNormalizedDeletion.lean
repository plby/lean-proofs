/- The unique-linkage alternative with retained column witnesses. -/
import ErdosProblems.Erdos73.RichGrill
import ErdosProblems.Erdos73.ColumnMinorTransport

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open Erdos73Infrastructure.SimpleGraph

def controlledGrillRows (g : ℕ) : ℕ := qualitativeGrillRows (2 * g) (g * g + 1)
def controlledGrillColumns (g : ℕ) : ℕ := qualitativeGrillColumns (2 * g) (g * g + 1)

theorem controlledGrillRows_pos (g : ℕ) : 0 < controlledGrillRows g :=
  qualitativeGrillRows_pos _ _

/-- The normalized alternative yields a grid with actual witnesses on
`2*g` distinct original columns in every row, unless a packing survives. -/
theorem unique_linkage_avoiding_column_of_no_richGrid
    {V I : Type*} [Fintype V] [Fintype I] {G : SimpleGraph V} {A B : Finset V}
    (R : PerfectPathPacking G A B) (hunique : R.IsUniqueLinkage)
    (Q : I → Finset V) (hne : ∀ i, (Q i).Nonempty)
    (hconn : ∀ i, (G.induce (Q i : Set V)).Connected)
    (hdisj : Pairwise fun i j => Disjoint (Q i) (Q j))
    (g : ℕ) (hm : controlledGrillRows g ≤ R.card)
    (hsize : (R.card + 1) * (2 * controlledGrillColumns g) ≤ Fintype.card I)
    (hgrid : ¬ ColumnRichGrid G Q g) :
    ∃ i, ∃ P : PathPacking G (A \ Q i) (B \ Q i),
      R.card / (2 * controlledGrillRows g) + 1 ≤ P.card ∧
        ∀ r, Disjoint (P.path r).vertexSet (Q i) := by
  let k := R.card / (2 * controlledGrillRows g) + 1
  rcases pregrill_or_avoiding_linkage_of_unique_with_columns R hunique Q hne hconn hdisj
      (2 * controlledGrillColumns g) k hsize with havoid | ⟨P, e, he⟩
  · exact havoid
  · have hd : 2 * controlledGrillRows g * (k - 1) ≤ R.card := by
      dsimp only [k]
      rw [Nat.add_sub_cancel, Nat.mul_comm]
      exact Nat.div_mul_le_self _ _
    have hrich : ColumnRichGrid G P.column g := by
      rcases pregrill_has_columnRich_grid_or_bipartite P g (g * g + 1)
          (Nat.succ_pos _) hm hd le_rfl with hg | hb
      · exact hg
      · exact hb.toGrid
    exact (hgrid (hrich.reindex e (fun j => (he j).subset))).elim

end
end Erdos73
