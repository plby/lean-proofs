import ErdosProblems.Erdos633.BoundaryPointGeometry

/-!
# Local angle sums at all vertices of a congruent tiling

A tile through whose open edge the vertex passes contributes a straight
angle. The sector partition accounts for these contributions explicitly.
There is at most one such tile at a dissection vertex. Every nonouter
vertex therefore has a corner-angle sum of either pi or twice pi.
-/

namespace Erdos633

open scoped BigOperators

noncomputable def CongruentTiling.straightCount {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (z : ℂ) : ℕ := by
  classical
  exact (Finset.univ.filter fun i : Fin N =>
    z ∈ (T.labelledTile i).carrier ∧ z ∉ Set.range (T.labelledTile i).vertex).card

open Classical in
theorem CongruentTiling.sum_straight_indicator {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (z : ℂ) :
    (∑ i : Fin N, if z ∈ (T.labelledTile i).carrier ∧
      z ∉ Set.range (T.labelledTile i).vertex then Real.pi else 0) =
      (T.straightCount z : ℝ) * Real.pi := by
  classical
  rw [← Finset.sum_filter]
  simp [CongruentTiling.straightCount]

theorem CongruentTiling.dissection_vertex_mem_carrier {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (z : ℂ) (hz : z ∈ T.labelledDissection.vertexFinset) :
    z ∈ P.carrier := by
  obtain ⟨i, k, hk⟩ := (T.labelledDissection.mem_vertexFinset z).mp hz
  rw [← hk]
  exact T.labelledDissection.tile_subset i ((T.labelledTile i).vertex_mem_carrier k)

open Classical in
theorem CongruentTiling.local_angle_contribution {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (z : ℂ) (hz : z ∈ T.labelledDissection.vertexFinset)
    (i : Fin N) :
    2 * (if z ∈ (T.labelledTile i).carrier then (T.labelledTile i).localSectorArea z else 0) =
      (∑ k : Fin 3, if (T.labelledTile i).vertex k = z then R.cornerAngle k else 0) +
        if z ∈ (T.labelledTile i).carrier ∧ z ∉ Set.range (T.labelledTile i).vertex then
          Real.pi else 0 := by
  classical
  by_cases hv : z ∈ Set.range (T.labelledTile i).vertex
  · obtain ⟨k, rfl⟩ := hv
    have hm := (T.labelledTile i).vertex_mem_carrier k
    have hn : ¬ ((T.labelledTile i).vertex k ∈ (T.labelledTile i).carrier ∧
        (T.labelledTile i).vertex k ∉ Set.range (T.labelledTile i).vertex) :=
      fun h => h.2 ⟨k, rfl⟩
    rw [if_pos hm, if_neg hn]
    simp only [(T.labelledTile i).vertex_injective.eq_iff, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, add_zero]
    rw [Triangle.localSectorArea_vertex, T.labelledTile_cornerAngle]
    ring
  · have hc : (∑ k : Fin 3,
        if (T.labelledTile i).vertex k = z then R.cornerAngle k else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      exact if_neg (fun h => hv ⟨k, h⟩)
    rw [hc, zero_add]
    by_cases hm : z ∈ (T.labelledTile i).carrier
    · rw [if_pos hm, if_pos ⟨hm, hv⟩,
        (T.labelledTile i).localSectorArea_boundary_nonvertex z hm
          (T.labelledDissection.vertex_not_mem_tile_interior z hz i) hv]
      ring
    · rw [if_neg hm, if_neg (fun h => hm h.1)]
      ring

theorem CongruentTiling.local_angle_balance {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (z : ℂ) (hz : z ∈ T.labelledDissection.vertexFinset) :
    2 * P.localSectorArea z = T.angleSumAt z + (T.straightCount z : ℝ) * Real.pi := by
  classical
  have harea := T.labelledDissection.localSectorArea_eq_sum_ite z
    (T.dissection_vertex_mem_carrier z hz)
  rw [harea, Finset.mul_sum]
  change (∑ i : Fin N, 2 * (if z ∈ (T.labelledTile i).carrier then
    (T.labelledTile i).localSectorArea z else 0)) =
      T.angleSumAt z + (T.straightCount z : ℝ) * Real.pi
  simp_rw [T.local_angle_contribution z hz]
  rw [Finset.sum_add_distrib, T.sum_straight_indicator,
    ← T.sum_cornerCount_mul z R.cornerAngle]
  rfl

theorem CongruentTiling.straightCount_le_one {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (z : ℂ) (hz : z ∈ T.labelledDissection.vertexFinset) :
    T.straightCount z ≤ 1 := by
  by_contra h
  have hn : 2 ≤ T.straightCount z := by omega
  have hnreal : (2 : ℝ) ≤ T.straightCount z := by exact_mod_cast hn
  have hp := mul_le_mul_of_nonneg_right hnreal Real.pi_pos.le
  have hbal := T.local_angle_balance z hz
  have hpos := T.angleSumAt_pos_of_vertex z hz
  have hbound := P.localSectorArea_le_pi z
  linarith

theorem CongruentTiling.nonouter_angleSumAt {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (z : ℂ) (hz : z ∈ T.labelledDissection.vertexFinset)
    (houter : z ∉ Set.range P.vertex) :
    T.angleSumAt z = Real.pi ∨ T.angleSumAt z = 2 * Real.pi := by
  have hbal := T.local_angle_balance z hz
  have hpos := T.angleSumAt_pos_of_vertex z hz
  have hn := T.straightCount_le_one z hz
  have hcases : T.straightCount z = 0 ∨ T.straightCount z = 1 := by omega
  by_cases hi : z ∈ interior P.carrier
  · rw [P.localSectorArea_interior z hi] at hbal
    rcases hcases with h | h
    · rw [h, Nat.cast_zero, zero_mul, add_zero] at hbal
      exact Or.inr hbal.symm
    · rw [h, Nat.cast_one, one_mul] at hbal
      exact Or.inl (by linarith)
  · rw [P.localSectorArea_boundary_nonvertex z
      (T.dissection_vertex_mem_carrier z hz) hi houter] at hbal
    rcases hcases with h | h
    · rw [h, Nat.cast_zero, zero_mul, add_zero] at hbal
      exact Or.inl (by linarith)
    · rw [h, Nat.cast_one, one_mul] at hbal
      linarith

noncomputable def CongruentTiling.localAngleMultiplier {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (z : ℂ) : ℕ := by
  classical
  exact if T.angleSumAt z = Real.pi then 1 else 2

theorem CongruentTiling.localAngleMultiplier_bounds {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (z : ℂ) :
    1 ≤ T.localAngleMultiplier z ∧ T.localAngleMultiplier z ≤ 2 := by
  classical
  unfold CongruentTiling.localAngleMultiplier
  split_ifs <;> norm_num

theorem CongruentTiling.localAngleMultiplier_equation {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (z : ℂ) (hz : z ∈ T.labelledDissection.vertexFinset)
    (houter : z ∉ Set.range P.vertex) :
    T.angleSumAt z = (T.localAngleMultiplier z : ℝ) * Real.pi := by
  classical
  by_cases h : T.angleSumAt z = Real.pi
  · simp [CongruentTiling.localAngleMultiplier, h]
  · rcases T.nonouter_angleSumAt z hz houter with h₁ | h₂
    · exact False.elim (h h₁)
    · simp only [CongruentTiling.localAngleMultiplier, if_neg h, Nat.cast_ofNat]
      exact h₂

end Erdos633
