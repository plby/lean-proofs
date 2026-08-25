import StackExchange.Puzzling139335.N5.Normalized

/-!
# Diagonal reflection with the two double-corner pieces exchanged

This is a physical symmetry of the whole dissection followed by a relabeling.
The normalized diagonal pair is left unchanged as actual subsets of the plane,
while the singleton and cornerless pieces are reflected. In particular, a
top-side contact condition on the fourth piece becomes a right-side condition.
-/

open Set

namespace Puzzling139335.N5.FourthSide

open ReflectionSeparation

noncomputable section

/-- Reflect the whole dissection in the main diagonal and exchange labels
zero and one. -/
def diagonalSwap (d : SquareDissection) : SquareDissection :=
  (d.map diagonal diagonal_image_unitSquare).reindex (Equiv.swap 0 1)

theorem diagonalSwap_piece (d : SquareDissection) (i : Fin 4) :
    (diagonalSwap d).piece i = diagonal '' d.piece (Equiv.swap 0 1 i) := rfl

@[simp] theorem diagonalSwap_piece_zero_image (d : SquareDissection) :
    (diagonalSwap d).piece 0 = diagonal '' d.piece 1 := by
  rw [diagonalSwap_piece, Equiv.swap_apply_left]

@[simp] theorem diagonalSwap_piece_one_image (d : SquareDissection) :
    (diagonalSwap d).piece 1 = diagonal '' d.piece 0 := by
  rw [diagonalSwap_piece, Equiv.swap_apply_right]

@[simp] theorem diagonalSwap_piece_two (d : SquareDissection) :
    (diagonalSwap d).piece 2 = diagonal '' d.piece 2 := by
  rw [diagonalSwap_piece]
  have hswap : Equiv.swap (0 : Fin 4) 1 2 = 2 := by decide
  rw [hswap]

@[simp] theorem diagonalSwap_piece_three (d : SquareDissection) :
    (diagonalSwap d).piece 3 = diagonal '' d.piece 3 := by
  rw [diagonalSwap_piece]
  have hswap : Equiv.swap (0 : Fin 4) 1 3 = 3 := by decide
  rw [hswap]

/-- The source is exactly unchanged, not merely congruent to the old source. -/
theorem diagonalSwap_piece_zero {d : SquareDissection} (h : Normalized d) :
    (diagonalSwap d).piece 0 = d.piece 0 := by
  rw [diagonalSwap_piece_zero_image, ← h.diagonal_image, Set.image_image]
  simp

theorem diagonalSwap_piece_one {d : SquareDissection} (h : Normalized d) :
    (diagonalSwap d).piece 1 = d.piece 1 := by
  rw [diagonalSwap_piece_one_image, h.diagonal_image]

theorem diagonalSwap_tileCornerCount (d : SquareDissection) (i : Fin 4) :
    (diagonalSwap d).tileCornerCount i = d.tileCornerCount (Equiv.swap 0 1 i) := by
  change (d.map diagonal diagonal_image_unitSquare).tileCornerCount (Equiv.swap 0 1 i) = _
  exact tileCornerCount_map d diagonal diagonal_image_unitSquare _

/-- The same raw normalized corner data hold after the physical transformation. -/
theorem diagonalSwap_normalized {d : SquareDissection} (h : Normalized d) :
    Normalized (diagonalSwap d) := by
  constructor
  · rw [diagonalSwap_tileCornerCount, Equiv.swap_apply_left, h.count_one]
  · rw [diagonalSwap_tileCornerCount, Equiv.swap_apply_right, h.count_zero]
  · rw [diagonalSwap_tileCornerCount]
    have hswap : Equiv.swap (0 : Fin 4) 1 2 = 2 := by decide
    rw [hswap, h.count_two]
  · rw [diagonalSwap_tileCornerCount]
    have hswap : Equiv.swap (0 : Fin 4) 1 3 = 3 := by decide
    rw [hswap, h.count_three]
  · rw [diagonalSwap_piece_zero h]
    exact h.bottom_left
  · rw [diagonalSwap_piece_zero h]
    exact h.bottom_right
  · rw [diagonalSwap_piece_zero h, diagonalSwap_piece_one h]
    exact h.diagonal_image
  · rw [diagonalSwap_piece_two]
    refine ⟨corner 2, h.top_right, ?_⟩
    apply diagonal_fixed
    norm_num [corner, Fin.ext_iff]

@[simp] theorem diagonalSwap_hasProtectedCenter (d : SquareDissection) :
    (diagonalSwap d).HasProtectedCenter ↔ d.HasProtectedCenter := by
  unfold diagonalSwap
  rw [SquareDissection.reindex_hasProtectedCenter, SquareDissection.map_hasProtectedCenter]

/-- An actual singleton congruence is transported by postcomposing with the
diagonal reflection; the source set itself does not move. -/
theorem diagonalSwap_singleton_image {d : SquareDissection} (h : Normalized d)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece 2) :
    (e.trans diagonal) '' (diagonalSwap d).piece 0 = (diagonalSwap d).piece 2 := by
  rw [diagonalSwap_piece_zero h, diagonalSwap_piece_two]
  change (fun p : Plane => diagonal (e p)) '' d.piece 0 = diagonal '' d.piece 2
  rw [← Set.image_image, he]

/-- A top contact set with at most one point becomes a right contact set
with at most one point under the common diagonal reflection. -/
theorem diagonalSwap_right_subsingleton_of_top (d : SquareDissection)
    (hTop : (d.piece 3 ∩ {p : Plane | p 1 = 1}).Subsingleton) :
    ((diagonalSwap d).piece 3 ∩ {p : Plane | p 0 = 1}).Subsingleton := by
  rintro p ⟨hp, hpRight⟩ q ⟨hq, hqRight⟩
  rw [diagonalSwap_piece_three] at hp hq
  obtain ⟨a, ha, rfl⟩ := hp
  obtain ⟨b, hb, rfl⟩ := hq
  change a 1 = 1 at hpRight
  change b 1 = 1 at hqRight
  exact congrArg diagonal (hTop ⟨ha, hpRight⟩ ⟨hb, hqRight⟩)

/-- Either the original dissection or its physical diagonal-swap image has
the desired right-side contact condition. -/
theorem exists_right_subsingleton_choice {d : SquareDissection} (h : Normalized d)
    (hSides : (d.piece 3 ∩ {p : Plane | p 0 = 1}).Subsingleton ∨
      (d.piece 3 ∩ {p : Plane | p 1 = 1}).Subsingleton) :
    ∃ d' : SquareDissection, Normalized d' ∧ d'.piece 0 = d.piece 0 ∧
      (d'.HasProtectedCenter ↔ d.HasProtectedCenter) ∧
      (d'.piece 3 ∩ {p : Plane | p 0 = 1}).Subsingleton ∧
      (d' = d ∨ d' = diagonalSwap d) := by
  rcases hSides with hRight | hTop
  · exact ⟨d, h, rfl, Iff.rfl, hRight, Or.inl rfl⟩
  · exact ⟨diagonalSwap d, diagonalSwap_normalized h, diagonalSwap_piece_zero h,
      diagonalSwap_hasProtectedCenter d, diagonalSwap_right_subsingleton_of_top d hTop,
      Or.inr rfl⟩

theorem exists_right_subsingleton {d : SquareDissection} (h : Normalized d)
    (hSides : (d.piece 3 ∩ {p : Plane | p 0 = 1}).Subsingleton ∨
      (d.piece 3 ∩ {p : Plane | p 1 = 1}).Subsingleton) :
    ∃ d' : SquareDissection, Normalized d' ∧ d'.piece 0 = d.piece 0 ∧
      (d'.HasProtectedCenter ↔ d.HasProtectedCenter) ∧
      (d'.piece 3 ∩ {p : Plane | p 0 = 1}).Subsingleton := by
  obtain ⟨d', hd', hsource, hcenter, hright, _hchoice⟩ :=
    exists_right_subsingleton_choice h hSides
  exact ⟨d', hd', hsource, hcenter, hright⟩

end

end Puzzling139335.N5.FourthSide
