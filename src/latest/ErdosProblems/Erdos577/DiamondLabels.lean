import ErdosProblems.Erdos577.QuadDegrees

/-! Recover the low vertices of a five-edge quadrilateral from a second cyclic labeling. -/

namespace Erdos577.Quadrilateral

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
lemma missing_column_thirteen (q : Quadrilateral G) (z : V)
    (hrow : ∀ j : Fin 4, G.Adj z (q j) ↔ (13 : ℕ).testBit j.val = true)
    (u : V) (hu : u ∈ q.support) (hnot : ¬G.Adj z u) : u = q 1 := by
  obtain ⟨j, rfl⟩ := (q.mem_support u).mp hu
  have hmask : ∀ j : Fin 4, (13 : ℕ).testBit j.val = true ↔ j ≠ 1 := by decide +kernel
  have hj : j = 1 := by
    by_contra hh
    exact hnot ((hrow j).mpr ((hmask j).mpr hh))
  exact congrArg q hj

omit [DecidableRel G.Adj] in
lemma low_label_swap (q v : Quadrilateral G) (hs : v.support = q.support)
    (hdiag : G.Adj (q 0) (q 2)) (hnot : ¬G.Adj (v 1) (v 3))
    (he : v 3 = q 1) : v 1 = q 3 := by
  classical
  have hl : degreeIn G (v 1) v.support = 2 := by
    rw [v.degreeIn_eq]
    change 2 + (if G.Adj (v 1) (v 3) then 1 else 0) = 2
    rw [if_neg hnot]
  rw [hs] at hl
  have hn : v 1 ≠ q 1 := by
    rw [← he]
    exact fun hh ↦ (by decide : (1 : Fin 4) ≠ 3) (v.injective hh)
  obtain ⟨i, hi⟩ := (q.mem_support (v 1)).mp (hs ▸ (v.mem_support _).mpr ⟨1, rfl⟩)
  rw [← hi] at hl hn ⊢
  fin_cases i
  · have hh := q.degreeIn_eq 0
    change degreeIn G (q 0) q.support = 2 + (if G.Adj (q 0) (q 2) then 1 else 0) at hh
    rw [if_pos hdiag] at hh
    change degreeIn G (q 0) q.support = 2 at hl
    exact False.elim ((by decide : (2 : ℕ) ≠ 3) (hl.symm.trans hh))
  · exact False.elim (hn rfl)
  · have hh := q.degreeIn_eq 2
    change degreeIn G (q 2) q.support = 2 + (if G.Adj (q 2) (q 0) then 1 else 0) at hh
    rw [if_pos hdiag.symm] at hh
    change degreeIn G (q 2) q.support = 2 at hl
    exact False.elim ((by decide : (2 : ℕ) ≠ 3) (hl.symm.trans hh))
  · rfl

end Erdos577.Quadrilateral
