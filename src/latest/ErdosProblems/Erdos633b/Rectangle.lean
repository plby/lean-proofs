import ErdosProblems.Erdos633b.Patch
import ErdosProblems.Erdos633b.Quadratic

/-! A parallelogram grid tiled by `2 * m * n` rigid copies of an arbitrary triangle. -/

namespace Erdos633b

abbrev RectCell (m n : ℕ) := Bool × Fin m × Fin n

namespace RectCell

def toGrid {m n : ℕ} (c : RectCell m n) : GridCell (m + n) :=
  if c.1 then GridCell.down (m + n) c.2.1 c.2.2 (by omega)
  else GridCell.up (m + n) c.2.1 c.2.2 (by omega)

theorem toGrid_injective (m n : ℕ) : Function.Injective (toGrid (m := m) (n := n)) := by
  rintro ⟨b, i, j⟩ ⟨b', i', j'⟩ h
  cases b <;> cases b' <;> simp_all [toGrid, GridCell.up, GridCell.down, Fin.ext_iff]

theorem exists_interval (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : 0 ≤ x) (hxn : x ≤ n) :
    ∃ i : Fin n, (i : ℝ) ≤ x ∧ x ≤ (i : ℝ) + 1 := by
  by_cases hlt : x < n
  · have hf : ⌊x⌋₊ < n := by exact_mod_cast (Nat.floor_le hx).trans_lt hlt
    exact ⟨⟨⌊x⌋₊, hf⟩, Nat.floor_le hx, (Nat.lt_floor_add_one x).le⟩
  · have he : x = n := le_antisymm hxn (le_of_not_gt hlt)
    refine ⟨⟨n - 1, by omega⟩, ?_, ?_⟩ <;>
      simp only [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] <;> linarith

noncomputable def motion {m n : ℕ} (c : RectCell m n) (T : Triangle) :
    Plane ≃ᵃⁱ[ℝ] Plane := c.toGrid.motion T

theorem covers (T : Triangle) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    (⋃ c : RectCell m n, c.motion T '' T.support) =
      {p | 0 ≤ T.coord 1 p ∧ T.coord 1 p ≤ m ∧
        0 ≤ T.coord 2 p ∧ T.coord 2 p ≤ n} := by
  ext p
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨b, i, j⟩, hp⟩
    rw [motion, GridCell.mem_piece] at hp
    have hi : (i : ℝ) + 1 ≤ m := by exact_mod_cast i.isLt
    have hj : (j : ℝ) + 1 ≤ n := by exact_mod_cast j.isLt
    have hi0 : 0 ≤ (i : ℝ) := Nat.cast_nonneg _
    have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
    cases b <;> simp only [toGrid, Bool.false_eq_true, ↓reduceIte, GridCell.up,
      GridCell.down, GridCell.Closed] at hp <;>
      exact ⟨by linarith [hp.1, hp.2.1, hp.2.2],
        by linarith [hp.1, hp.2.1, hp.2.2],
        by linarith [hp.1, hp.2.1, hp.2.2],
        by linarith [hp.1, hp.2.1, hp.2.2]⟩
  · rintro ⟨hx, hxm, hy, hyn⟩
    obtain ⟨i, hi, hi'⟩ := exists_interval m hm (T.coord 1 p) hx hxm
    obtain ⟨j, hj, hj'⟩ := exists_interval n hn (T.coord 2 p) hy hyn
    by_cases hsum : T.coord 1 p + T.coord 2 p ≤ (i : ℝ) + (j : ℝ) + 1
    · refine ⟨(false, i, j), ?_⟩
      rw [motion, GridCell.mem_piece]
      exact ⟨hi, hj, hsum⟩
    · refine ⟨(true, i, j), ?_⟩
      rw [motion, GridCell.mem_piece]
      exact ⟨hi', hj', le_of_not_ge hsum⟩

theorem disjoint_interiors (T : Triangle) (m n : ℕ) :
    Pairwise fun c d : RectCell m n =>
      Disjoint (interior (c.motion T '' T.support)) (interior (d.motion T '' T.support)) := by
  intro c d hcd
  exact GridCell.disjoint_interiors T (m + n) ((toGrid_injective m n).ne hcd)

end RectCell

/-- The parallelogram spanned by integer multiples of the two edges at vertex zero. -/
noncomputable def rectangle_patch (T : Triangle) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    Patch T {p | 0 ≤ T.coord 1 p ∧ T.coord 1 p ≤ m ∧
      0 ≤ T.coord 2 p ∧ T.coord 2 p ≤ n} (2 * m * n) := by
  have d := Patch.ofFintype T _ (fun c : RectCell m n => c.motion T)
    (RectCell.covers T m n hm hn) (RectCell.disjoint_interiors T m n)
  simpa only [RectCell, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin, mul_assoc] using d

end Erdos633b
