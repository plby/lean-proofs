import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Tauto

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Finite shift graphs

This module begins the explicit large-odd-girth avoidance construction used in
Erdős Problem 593.  Vertices are strictly increasing finite tuples in a linear
order.  Two tuples are joined when one is obtained by shifting the other one
place along a common increasing tuple of length one greater.
-/

namespace Erdos593

universe u

namespace ShiftGraph

variable (κ : Type u) [LinearOrder κ]

/-- A strictly increasing tuple of length `r`. -/
abbrev Tuple (r : ℕ) := {f : Fin r → κ // StrictMono f}

/-- The directed one-place shift relation. -/
def Shift {r : ℕ} (x y : Tuple κ r) : Prop :=
  ∃ z : Tuple κ (r + 1),
    (∀ i : Fin r, x.1 i = z.1 i.castSucc) ∧
    (∀ i : Fin r, y.1 i = z.1 i.succ)

/-- The undirected shift graph on increasing `r`-tuples. -/
def graph (r : ℕ) : _root_.SimpleGraph (Tuple κ r) :=
  _root_.SimpleGraph.fromRel (Shift κ)

/-
A directed shift of a nonempty tuple changes the tuple.
-/
theorem ne_of_shift {r : ℕ} (hr : 0 < r) {x y : Tuple κ r}
    (h : Shift κ x y) : x ≠ y := by
  obtain ⟨ z, hx, hy ⟩ := h;
  contrapose! hr;
  rcases r with ( _ | r ) <;> simp_all +decide [ Fin.forall_fin_succ, StrictMono ];
  exact absurd hx.1 ( ne_of_gt ( z.2 ( by simp +decide ) ) )

/-
Every displayed directed shift of a nonempty tuple is an edge of the
undirected shift graph.
-/
theorem adj_of_shift {r : ℕ} (hr : 0 < r) {x y : Tuple κ r}
    (h : Shift κ x y) : (graph κ r).Adj x y := by
  -- Apply the hypothesis `h_ne` to the assumption `a`.
  apply (ne_of_shift κ hr h) |> fun h_ne => by tauto;

/-
For positive tuple length, adjacency in a shift graph is exactly a shift
in one of the two directions.
-/
theorem adj_iff_shift_or_shift {r : ℕ} (hr : 0 < r) {x y : Tuple κ r} :
    (graph κ r).Adj x y ↔ Shift κ x y ∨ Shift κ y x := by
  simp +decide [ graph ];
  rintro ( h | h ) <;> [ exact ne_of_shift κ hr h; exact ne_of_shift κ hr h |> Ne.symm ]

/-
The first shift graph is the complete graph on increasing one-tuples.
-/
theorem graph_one_eq_completeGraph :
    graph κ 1 = _root_.SimpleGraph.completeGraph (Tuple κ 1) := by
  ext x y;
  simp +decide [ graph, SimpleGraph.fromRel_adj ];
  intro hxy; cases lt_or_gt_of_ne ( show x.1 0 ≠ y.1 0 from by contrapose! hxy; ext i; fin_cases i; aesop ) <;> [ left; right ] <;> use ⟨ Fin.cons ( if x.1 0 < y.1 0 then x.1 0 else y.1 0 ) ( if x.1 0 < y.1 0 then y.1 else x.1 ), ?_ ⟩ <;> simp +decide [ *, Fin.forall_fin_succ ] ;
  · simp +decide [ StrictMono, Fin.forall_fin_succ ];
    assumption;
  · grind;
  · simp +decide [ *, StrictMono, Fin.forall_fin_succ ];
    split_ifs <;> simp_all +decide [ lt_asymm ]

end ShiftGraph

end Erdos593
