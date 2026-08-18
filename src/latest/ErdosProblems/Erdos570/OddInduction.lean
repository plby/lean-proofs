/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.Components
import ErdosProblems.Erdos570.OddArithmetic

/-!
# Structural steps in the strengthened odd-cycle induction

This module contains the target-graph induction steps that do not depend on
the special geometry of an odd cycle.  In particular, it formalizes the
published disconnected-target reduction with the decreasing square-root
correction intact.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

open Erdos79

/-- In a strong edge-count induction, a target having a connected component
with between two and `m-1` edges is forced at the full `m`-edge budget.

The component is found first in the whole host.  Its image is then removed,
and the exact component vertex bound supplies room for the remaining union
of components. -/
theorem ramseyAt_oddBudget_of_nontrivial_component
    {F H : GraphCode} {B s m : ℕ} (hH : NoIsolated H)
    (hm : H.edgeCount = m) (c : H.graph.ConnectedComponent)
    (hc2 : 2 ≤ (componentCode H c).edgeCount)
    (hcm : (componentCode H c).edgeCount < m)
    (hIH : ∀ Q : GraphCode, NoIsolated Q → Q.edgeCount < m →
      graphRamseyNumber F Q ≤ oddBudget B s Q.edgeCount) :
    RamseyAt F H (oddBudget B s m) := by
  let C := componentCode H c
  let R := componentRemainderCode H c
  have hC2 : 2 ≤ C.edgeCount := by simpa [C] using hc2
  have hsplit := componentCode_edgeCount_add_remainder H c
  have hCle : C.edgeCount ≤ m := by
    dsimp only [C]
    rw [← hm]
    omega
  have hCno : NoIsolated C := componentCode_noIsolated c (by omega)
  have hCram : graphRamseyNumber F C ≤ oddBudget B s m :=
    (hIH C hCno (by simpa [C] using hcm)).trans (oddBudget_mono hCle)
  have hfirst : RamseyAt F C (oddBudget B s m) :=
    ramseyAt_of_graphRamseyNumber_le hCram
  have hRedge : R.edgeCount = m - C.edgeCount := by
    dsimp only [C, R]
    omega
  have hRlt : R.edgeCount < m := by
    rw [hRedge]
    omega
  have hRno : NoIsolated R := componentRemainderCode_noIsolated hH c
  have hRram : graphRamseyNumber F R ≤ oddBudget B s R.edgeCount :=
    hIH R hRno hRlt
  have hCvertices : C.vertexCount ≤ C.edgeCount + 1 :=
    componentCode_vertexCount_le_edgeCount_add_one H c
  have hbudget : oddBudget B s R.edgeCount + C.vertexCount ≤
      oddBudget B s m := by
    rw [hRedge]
    exact oddBudget_sub_add_component_order_le hC2 hCle hCvertices
  have hRroom : graphRamseyNumber F R ≤
      oddBudget B s m - C.vertexCount := by
    omega
  have hsecond : RamseyAt F R (oddBudget B s m - C.vertexCount) :=
    ramseyAt_of_graphRamseyNumber_le hRroom
  have hunion : RamseyAt F (disjointUnionCode C R) (oddBudget B s m) :=
    ramseyAt_disjointUnion_remove_first hfirst hsecond
  exact hunion.mono_right (by
    simpa [C, R] using isContained_component_partition H c)

end Erdos570
