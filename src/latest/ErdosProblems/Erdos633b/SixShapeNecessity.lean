import ErdosProblems.Erdos633b.IncommensurableShapes
import ErdosProblems.Erdos633b.ShapeNecessity
import ErdosProblems.Erdos633b.ReptilingNecessity

/-! Assemble the exact case conditions for the exhaustive incommensurable
angle classification once the reference side ratios are rational. The
side-rationality theorem is a remaining separate proof obligation. -/

namespace Erdos633b

theorem eightCases_of_not_injective_angles (T : Triangle)
    (h : ¬ Function.Injective T.angle) : EightCases T := by
  by_cases h01 : T.angle 0 = T.angle 1
  · exact ⟨Equiv.refl _, Or.inl h01⟩
  by_cases h02 : T.angle 0 = T.angle 2
  · refine ⟨Equiv.swap 1 2, Or.inl ?_⟩
    exact h02
  by_cases h12 : T.angle 1 = T.angle 2
  · refine ⟨(Equiv.swap 0 1).trans (Equiv.swap 0 2), Or.inl ?_⟩
    exact h12
  exfalso
  apply h
  intro i j he
  fin_cases i <;> fin_cases j <;> simp_all

theorem Triangle.RationalSides.reindex {S : Triangle} (hs : S.RationalSides)
    (e : Equiv.Perm (Fin 3)) : Triangle.RationalSides (S.reindex e) := by
  intro i j
  rw [Triangle.side_reindex, Triangle.side_reindex]
  exact hs (e.symm i) (e.symm j)

namespace Tiling

theorem six_shapes_necessary_of_rational_sides {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) (hs : d.tile.RationalSides) (hshape : SixAngleShapes d.tile T) :
    EightCases T := by
  obtain ⟨e, f, hshape⟩ := hshape
  let U : Triangle := T.reindex f
  let d' : Tiling U n := (d.reindexTile e).reindexOuter f
  have hs' : d'.tile.RationalSides := hs.reindex e
  change GroupOneShape d'.tile U ∨ GroupTwoShape d'.tile U at hshape
  apply eightCases_of_reindex T f
  change EightCases U
  rcases hshape with ⟨_, hshape⟩ | ⟨hg, hshape⟩
  · rcases hshape with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
    · exact case_six_of_groupOne_shape d'.tile U hs' h0 h1 h2
    · exact d'.case_seven_necessary_of_groupOne hn hs' h0 h1 h2
  · rcases hshape with ⟨h0, h1, _⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, _⟩ | ⟨h0, _, h2⟩
    · exact case_five_of_groupTwo_shape d'.tile U hs' hg h0 h1
    · exact case_eight_of_groupTwo_shape d'.tile U hs' hg h0 h1 h2
    · exact case_four_of_groupTwo_third_shape d'.tile U hs' hg h0 h1
    · exact case_four_of_groupTwo_fourth_shape d'.tile U hs' hg h0 h2

theorem incommensurable_necessary_of_rational_sides {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) (hirr : ¬ ∀ i, IsRational (T.angle i / Real.pi))
    (hs : d.tile.RationalSides) : EightCases T := by
  by_cases hscalene : Function.Injective T.angle
  · rcases d.incommensurable_scalene_angle_classification hirr hscalene with hrep | hshape
    · exact d.reptiling_necessary hn hrep
    · exact d.six_shapes_necessary_of_rational_sides hn hs hshape
  · exact eightCases_of_not_injective_angles T hscalene

end Tiling
end Erdos633b
