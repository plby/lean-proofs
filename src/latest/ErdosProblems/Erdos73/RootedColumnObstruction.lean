/- A minor obstruction restricted to column families meeting a fixed boundary. -/
import ErdosProblems.Erdos73.RichLinkageDeletion

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open Erdos73Infrastructure.SimpleGraph

variable {V : Type*} {G H : SimpleGraph V} {Z : Finset V} {g : ℕ}

/-- The index type may be arbitrary and is not required to be finite:
the rich-grid witnesses themselves use only a finite set of indices. -/
def NoRootedColumnRichGrid (G : SimpleGraph V) (Z : Finset V) (g : ℕ) : Prop :=
  ∀ (I : Type) (Q : I → Finset V),
    (∀ i, (G.induce (Q i : Set V)).Connected) →
    (Pairwise fun i j => Disjoint (Q i) (Q j)) →
    (∀ i, ∃ v ∈ Q i, v ∈ Z) → ¬ ColumnRichGrid G Q g

theorem NoRootedColumnRichGrid.mono (h : NoRootedColumnRichGrid G Z g) (hHG : H ≤ G) :
    NoRootedColumnRichGrid H Z g := by
  intro I Q hconn hdisj hroot hgrid
  have hconnG (i : I) : (G.induce (Q i : Set V)).Connected :=
    SimpleGraph.Connected.mono (fun _ _ h => hHG h) (hconn i)
  exact h I Q hconnG hdisj hroot (hgrid.mono hHG)

theorem noRootedColumnRichGrid_of_no_controlledGrid [Fintype V]
    {β : Finset (Finset V)} {q : ℕ} (h : BrambleHaven G β q)
    {A B : Finset V} (hAB : IsVertexSeparation G A B)
    (hpoint : h.PointsTo A B) (hmin : h.ForwardMinimal A B)
    (hsize : (A ∩ B).card + g ≤ q)
    (hno : ¬ ∃ M : MinorModel (squareGrid g) G, NoGridRowInHavenSmallSide h M) :
    NoRootedColumnRichGrid G (A ∩ B) g := by
  intro I Q hconn hdisj hroot hgrid
  obtain ⟨M, hM⟩ := hgrid
  exact hno ⟨M, noGridRowInHavenSmallSide_of_column_witnesses h hAB hpoint hmin
    hsize Q hconn hdisj hroot M hM⟩

end
end Erdos73
