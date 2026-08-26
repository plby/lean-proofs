import ErdosProblems.Erdos633.ReptileStarMatrix
import ErdosProblems.Erdos633.RightReptileCorners
import ErdosProblems.Erdos633.ExceptionalNecessity

/-!
# Necessity for actual irrational right-triangle tilings

The boundary counts and the two acute-corner alternatives are geometric.
The negative similarity eigenvalue excludes both unchanged corner matchings,
forcing a star matrix and the exact count `p²+q²`. The result is transported
through arbitrary outer and reference vertex permutations and combined with
the completed nonreptile branch.
-/

namespace Erdos633

open scoped BigOperators

theorem CongruentTiling.irrational_right_reptile_integer_ratio_ordered
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hN : ¬ IsSquare N) (hR : ¬ R.CommensurableAngles)
    (hC : R.angleC = Real.pi / 2)
    (hA : P.angleA = R.angleA) (hB : P.angleB = R.angleB) :
    P.angleC = Real.pi / 2 ∧ ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ N = p ^ 2 + q ^ 2 ∧
      dist P.b P.c / dist P.a P.c = (p : ℝ) / q := by
  obtain ⟨x, hx, hab, hac, hbc⟩ := P.scaled_sides_of_angles_eq R hA hB
  obtain ⟨e, he⟩ := P.isometry_of_scaled_sides R x hx hab hac hbc
  have hsq := T.similarity_scale_squared x hx e he
  have hside (i : Fin 3) : P.sideLength i = x * R.sideLength i := by
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi with rfl | rfl | rfl
    · exact hbc
    · change dist P.c P.a = x * dist R.c R.a
      rw [dist_comm P.c P.a, dist_comm R.c R.a]
      exact hac
    · exact hab
  have hmatrix (i : Fin 3) :
      ∑ j : Fin 3, (T.boundarySideCount i j : ℝ) * R.sideLength j = x * R.sideLength i :=
    (T.boundary_side_count_equation i).symm.trans (hside i)
  obtain ⟨hcornerA, hcornerB⟩ := T.right_acute_boundary_alternatives hR hC hA hB
  obtain ⟨p, q, hp, hq, hcount, hratio⟩ := natural_matrix_right_necessity_of_corner_alternatives
    T.boundarySideCount R.sideLength x N R.sideLength_pos hx hsq hN hmatrix
    (R.right_sideLength_pythagoras hC) hcornerA hcornerB
  have hratioP : P.sideLength 0 / P.sideLength 1 = (p : ℝ) / q := by
    rw [hside 0, hside 1, mul_div_mul_left _ _ (ne_of_gt hx)]
    exact hratio
  refine ⟨by linarith [P.angle_sum, R.angle_sum], p, q, hp, hq, hcount, ?_⟩
  rw [dist_comm P.a P.c]
  exact hratioP

theorem CongruentTiling.irrational_right_reptile_hasListedNonsquareShape
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hN : ¬ IsSquare N) (hR : ¬ R.CommensurableAngles)
    (hC : R.angleC = Real.pi / 2)
    (h : PermutedTriple P.cornerAngle R.cornerAngle) : HasListedNonsquareShape P := by
  obtain ⟨e, he⟩ := h
  let Q := P.relabel e
  let U : CongruentTiling Q R N := T.of_carrier_eq (P.relabel_carrier e).symm
  have hA : Q.angleA = R.angleA := (P.cornerAngle_relabel e 0).trans (he 0)
  have hB : Q.angleB = R.angleB := (P.cornerAngle_relabel e 1).trans (he 1)
  obtain ⟨hQC, p, q, hp, hq, hcount, hratio⟩ :=
    U.irrational_right_reptile_integer_ratio_ordered hN hR hC hA hB
  refine ⟨Q, P.relabel_carrier e, Or.inr (Or.inl ⟨hQC, p, q, hp, hq, hratio, ?_⟩)⟩
  simpa only [← hcount] using hN

theorem CongruentTiling.hasListedNonsquareShape_of_irrational_right_reptile
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hN : ¬ IsSquare N) (hR : ¬ R.CommensurableAngles)
    (hright : ∃ k : Fin 3, R.cornerAngle k = Real.pi / 2)
    (h : PermutedTriple P.cornerAngle R.cornerAngle) : HasListedNonsquareShape P := by
  obtain ⟨k, hk⟩ := hright
  let e : Equiv.Perm (Fin 3) := Equiv.swap k 2
  let S := R.relabel e
  let U : CongruentTiling P S N := T.of_reference_carrier_eq (R.relabel_carrier e)
  have hS : ¬ S.CommensurableAngles := fun hc => hR ((R.commensurableAngles_relabel_iff e).mp hc)
  have hSC : S.angleC = Real.pi / 2 := by
    have hc := R.cornerAngle_relabel e 2
    change S.angleC = R.cornerAngle (e 2) at hc
    simpa only [e, Equiv.swap_apply_right, hk] using hc
  have hRS : PermutedTriple R.cornerAngle S.cornerAngle := by
    refine ⟨e, ?_⟩
    intro j
    exact (R.cornerAngle_relabel e j).symm
  exact U.irrational_right_reptile_hasListedNonsquareShape hN hS hSC (h.trans hRS)

theorem CongruentTiling.hasListedNonsquareShape_of_irrational_right_tile
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hN : ¬ IsSquare N) (hR : ¬ R.CommensurableAngles)
    (hright : ∃ k : Fin 3, R.cornerAngle k = Real.pi / 2) : HasListedNonsquareShape P := by
  rcases T.permuted_angles_or_listed_of_irrational hN hR with h | h
  · exact T.hasListedNonsquareShape_of_irrational_right_reptile hN hR hright h
  · exact h

end Erdos633
