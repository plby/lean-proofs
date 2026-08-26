import ErdosProblems.Erdos73.BrickTileArray

/-! Exact gap regions between adjacent tiles, and their pairwise separation. -/

namespace Erdos73.BrickTileArray
noncomputable section
open scoped Classical

open SimpleGraph Finset

variable {c r C R : ℕ} (A : BrickTileArray c r C R)

def horizontalGap (i : Fin r) (j j' : Fin (2 * c)) : Finset (ElementaryWallVertex C R) :=
  univ.filter (fun w => w.val.1.val = 12 * A.row i + 4 ∧
    16 * A.column j + 10 ≤ w.val.2.val ∧ w.val.2.val ≤ 16 * A.column j' + 2)

def verticalGap (i i' : Fin r) (j : Fin (2 * c)) : Finset (ElementaryWallVertex C R) :=
  univ.filter (fun w => 12 * A.row i + 8 ≤ w.val.1.val ∧ w.val.1.val ≤ 12 * A.row i' ∧
    16 * A.column j + 6 ≤ w.val.2.val ∧ w.val.2.val ≤ 16 * A.column j + 7 ∧
    (w.val.1.val = 12 * A.row i' → w.val.2.val = 16 * A.column j + 6))

theorem mem_horizontalGap {i : Fin r} {j j' : Fin (2 * c)} {w : ElementaryWallVertex C R} :
    w ∈ A.horizontalGap i j j' ↔ w.val.1.val = 12 * A.row i + 4 ∧
      16 * A.column j + 10 ≤ w.val.2.val ∧ w.val.2.val ≤ 16 * A.column j' + 2 := by
  simp only [horizontalGap, mem_filter, mem_univ, true_and]

theorem mem_verticalGap {i i' : Fin r} {j : Fin (2 * c)} {w : ElementaryWallVertex C R} :
    w ∈ A.verticalGap i i' j ↔ 12 * A.row i + 8 ≤ w.val.1.val ∧
      w.val.1.val ≤ 12 * A.row i' ∧ 16 * A.column j + 6 ≤ w.val.2.val ∧
      w.val.2.val ≤ 16 * A.column j + 7 ∧
      (w.val.1.val = 12 * A.row i' → w.val.2.val = 16 * A.column j + 6) := by
  simp only [verticalGap, mem_filter, mem_univ, true_and]

theorem horizontalGap_inter_indices {i l : Fin r} {j j' t t' : Fin (2 * c)}
    (hj : j.val + 1 = j'.val) (ht : t.val + 1 = t'.val)
    {w : ElementaryWallVertex C R} (hw : w ∈ A.horizontalGap i j j')
    (hw' : w ∈ A.horizontalGap l t t') : i = l ∧ j = t ∧ j' = t' := by
  rw [A.mem_horizontalGap] at hw hw'
  have hil : i = l := A.row_strictMono.injective (by omega)
  have hjt : j = t := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with h | h
    · have hle : j' ≤ t := by change j'.val ≤ t.val; change j.val < t.val at h; omega
      have hc := A.column_strictMono.monotone hle
      omega
    · have hle : t' ≤ j := by change t'.val ≤ j.val; change t.val < j.val at h; omega
      have hc := A.column_strictMono.monotone hle
      omega
  exact ⟨hil, hjt, Fin.ext (by have hh := congrArg Fin.val hjt; omega)⟩

theorem verticalGap_inter_indices {i i' l l' : Fin r} {j t : Fin (2 * c)}
    (hi : i.val + 1 = i'.val) (hl : l.val + 1 = l'.val)
    {w : ElementaryWallVertex C R} (hw : w ∈ A.verticalGap i i' j)
    (hw' : w ∈ A.verticalGap l l' t) : i = l ∧ i' = l' ∧ j = t := by
  rw [A.mem_verticalGap] at hw hw'
  have hjt : j = t := A.column_strictMono.injective (by omega)
  have hil : i = l := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with h | h
    · have hle : i' ≤ l := by change i'.val ≤ l.val; change i.val < l.val at h; omega
      have hr := A.row_strictMono.monotone hle
      omega
    · have hle : l' ≤ i := by change l'.val ≤ i.val; change l.val < i.val at h; omega
      have hr := A.row_strictMono.monotone hle
      omega
  exact ⟨hil, Fin.ext (by have hh := congrArg Fin.val hil; omega), hjt⟩

theorem horizontalGap_disjoint_verticalGap (i l l' : Fin r) (j j' t : Fin (2 * c))
    (hj : j.val + 1 = j'.val) : Disjoint (A.horizontalGap i j j') (A.verticalGap l l' t) := by
  apply Finset.disjoint_left.mpr
  intro w hw hw'
  rw [A.mem_horizontalGap] at hw
  rw [A.mem_verticalGap] at hw'
  by_cases htj : t ≤ j
  · have hh := A.column_strictMono.monotone htj
    omega
  · have hle : j' ≤ t := by
      change j'.val ≤ t.val
      change ¬ t.val ≤ j.val at htj
      omega
    have hh := A.column_strictMono.monotone hle
    omega

end
end Erdos73.BrickTileArray
