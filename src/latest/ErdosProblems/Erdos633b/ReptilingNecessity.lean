import ErdosProblems.Erdos633b.ReptilingCounts
import ErdosProblems.Erdos633b.ReptilingOrdering
import ErdosProblems.Erdos633b.AngleRelations

/-! The necessary direction for every nonsquare reptiling, with arbitrary
vertex ordering and without a scalene assumption on the outer triangle. -/

namespace Erdos633b.Tiling

theorem reptiling_ordered_necessary {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) (h : ∀ i, d.tile.angle i = T.angle i)
    (h01 : d.tile.angle 0 < d.tile.angle 1) (h12 : d.tile.angle 1 < d.tile.angle 2) :
    EightCases T := by
  have hright : T.angle 2 = Real.pi / 2 :=
    (h 2).symm.trans (d.reptiling_right_angle hn h h01 h12)
  rcases d.reptiling_matrix_alternatives hn h h01 h12 with he | ⟨h01z, h10z⟩
  · obtain ⟨ha, hb, _⟩ := d.reptiling_triple_square hn h h01 h12 he
    have ha' : T.angle 0 = Real.pi / 6 := (h 0).symm.trans ha
    have hb' : T.angle 1 = Real.pi / 3 := (h 1).symm.trans hb
    refine ⟨Equiv.swap 1 2, Or.inr (Or.inr (Or.inl ?_))⟩
    simpa [Equiv.swap_apply_def] using And.intro ha' (And.intro hright hb')
  · obtain ⟨he, hf, hcount, hratio⟩ := d.reptiling_biquadratic hn h h01 h12 h01z h10z
    refine ⟨Equiv.refl _, Or.inr (Or.inl ?_)⟩
    exact ⟨hright, d.boundarySideCount 0 2, d.boundarySideCount 1 2,
      he, hf, hratio, hcount ▸ hn⟩

theorem reptiling_equal_angles_necessary {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) (h : ∀ i, d.tile.angle i = T.angle i) : EightCases T := by
  obtain ⟨e, he01, he12⟩ := three_values_ordered d.tile.angle
  let S : Triangle := T.reindex e.symm
  let d' : Tiling S n := (d.reindexOuter e.symm).reindexTile e.symm
  have hang (i : Fin 3) : d'.tile.angle i = d.tile.angle (e i) := by
    exact Triangle.angle_reindex d.tile e.symm i
  have hout (i : Fin 3) : S.angle i = T.angle (e i) := by
    exact Triangle.angle_reindex T e.symm i
  have heq (i : Fin 3) : d'.tile.angle i = S.angle i := by rw [hang, hout, h]
  apply eightCases_of_reindex T e.symm
  change EightCases S
  by_cases h01 : d'.tile.angle 0 = d'.tile.angle 1
  · refine ⟨Equiv.refl _, Or.inl ?_⟩
    simpa only [Equiv.refl_apply, heq] using h01
  by_cases h12 : d'.tile.angle 1 = d'.tile.angle 2
  · refine ⟨(Equiv.swap 0 1).trans (Equiv.swap 0 2), Or.inl ?_⟩
    simpa [Equiv.swap_apply_def, heq] using h12
  have h01' : d'.tile.angle 0 < d'.tile.angle 1 := by
    exact lt_of_le_of_ne (by simpa only [hang] using he01) h01
  have h12' : d'.tile.angle 1 < d'.tile.angle 2 := by
    exact lt_of_le_of_ne (by simpa only [hang] using he12) h12
  exact d'.reptiling_ordered_necessary hn heq h01' h12'

/-- A genuine nonsquare tiling by a triangle similar to its outer triangle
satisfies the eight-case classification. The similarity is expressed solely
by equality of angles up to a permutation, not by a classification predicate. -/
theorem reptiling_necessary {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n)
    (h : ∃ e : Equiv.Perm (Fin 3), ∀ i, T.angle i = d.tile.angle (e i)) :
    EightCases T := by
  obtain ⟨e, he⟩ := h
  let d' := d.reindexTile e.symm
  apply d'.reptiling_equal_angles_necessary hn
  intro i
  exact (Triangle.angle_reindex d.tile e.symm i).trans (he i).symm

theorem eightCases_of_independent_tile_angles {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) (hli : LinearIndependent ℚ d.tile.angle) : EightCases T :=
  d.reptiling_necessary hn (d.angles_permuted_of_linearIndependent hli)

end Erdos633b.Tiling
