import ErdosProblems.Erdos633b.Median
import ErdosProblems.Erdos633b.CaseSeven

/-! Sufficiency of the isosceles case via a genuine two-piece median dissection. -/

namespace Erdos633b

noncomputable def isosceles_tiling (T : Triangle)
    (hleg : dist (T.points 2) (T.points 0) = dist (T.points 2) (T.points 1)) : Tiling T 2 := by
  let R := T.firstHalf
  let S := T.secondHalf
  have hside : ∀ i, R.side i = S.side i := by
    intro i
    fin_cases i
    · change dist (T.firstHalf.points 1) (T.firstHalf.points 2) =
        dist (T.secondHalf.points 1) (T.secondHalf.points 2)
      rw [T.firstHalf_points, T.secondHalf_points]
      exact dist_left_midpoint_eq_dist_right_midpoint (𝕜 := ℝ) (T.points 0) (T.points 1)
    · change dist (T.firstHalf.points 2) (T.firstHalf.points 0) =
        dist (T.secondHalf.points 2) (T.secondHalf.points 0)
      rw [T.firstHalf_points, T.secondHalf_points]
      rfl
    · change dist (T.firstHalf.points 0) (T.firstHalf.points 1) =
        dist (T.secondHalf.points 0) (T.secondHalf.points 1)
      rw [T.firstHalf_points, T.secondHalf_points]
      exact hleg
  have hdist := R.distances_of_sides S hside
  let g := R.vertexIsometry S hdist
  have hg : g '' R.support = S.support := by
    rw [← R.support_move g]
    rw [R.move_vertexIsometry S hdist]
  let f : Fin 2 → Plane ≃ᵃⁱ[ℝ] Plane := ![AffineIsometryEquiv.refl ℝ Plane, g]
  have h0 : f 0 '' R.support = R.support := by
    change id '' R.support = R.support
    exact Set.image_id _
  have h1 : f 1 '' R.support = S.support := hg
  have hu : (⋃ i, f i '' R.support) = f 0 '' R.support ∪ f 1 '' R.support := by
    ext p
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact Or.inl hi
      · exact Or.inr hi
    · rintro (h | h)
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
  refine { tile := R, place := f, covers := ?_, disjoint_interiors := ?_ }
  · rw [hu, h0, h1]
    exact T.halves_cover
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change Disjoint (interior (f 0 '' R.support)) (interior (f 1 '' R.support))
      rw [h0, h1]
      exact T.halves_disjoint_interiors
    · change Disjoint (interior (f 1 '' R.support)) (interior (f 0 '' R.support))
      rw [h1, h0]
      exact T.halves_disjoint_interiors.symm
    · exact (hij rfl).elim

theorem case_one_sufficient (T : Triangle) (hangle : T.angle 0 = T.angle 1) :
    HasNonsquareTiling T := by
  have hsin : Real.sin (T.angle 1) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (T.angle_pos 1) (T.angle_lt_pi 1)).ne'
  have hside := T.sine_law 0 1
  rw [hangle] at hside
  have hside' : T.side 1 = T.side 0 := mul_left_cancel₀ hsin hside
  have hleg : dist (T.points 2) (T.points 0) = dist (T.points 2) (T.points 1) :=
    hside'.trans (dist_comm _ _)
  have hn : ¬ IsSquare (2 : ℕ) := by
    rintro ⟨k, hk⟩
    by_cases h : k ≤ 1
    · rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;> norm_num at hk
    · have hk2 : 2 ≤ k := by omega
      nlinarith
  exact ⟨2, hn, ⟨isosceles_tiling T hleg⟩⟩

theorem case_one_sufficient_reindexed (T : Triangle) (e : Equiv.Perm (Fin 3))
    (hangle : T.angle (e 0) = T.angle (e 1)) : HasNonsquareTiling T := by
  have result := case_one_sufficient (T.reindex e.symm)
    (by simpa only [Triangle.angle_reindex, Equiv.symm_symm] using hangle)
  exact hasNonsquareTiling_of_support_eq (T.support_reindex e.symm) result

end Erdos633b
