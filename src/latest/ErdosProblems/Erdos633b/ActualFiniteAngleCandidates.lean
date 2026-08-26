import ErdosProblems.Erdos633b.FiniteAngleCandidates
import ErdosProblems.Erdos633b.CornerAngleWeights

/-! Every hypothetical nonsquare counterexample has one of the 293 exact
ordered tile-angle triples. The surviving domain is not assumed empty. -/

namespace Erdos633b

def angleTableWeights (v : ℕ × ℕ × ℕ) : Fin 3 → ℕ :=
  ![v.2.1, v.2.2, v.1 - v.2.1 - v.2.2]

theorem angle_table_weights_bounds (v : ℕ × ℕ × ℕ) (hv : v ∈ finiteAngleCandidates) :
    (∀ i, 0 < angleTableWeights v i ∧ angleTableWeights v i < v.1) ∧
      ∑ i, angleTableWeights v i = v.1 := by
  obtain ⟨_, _, ha, hab, hsum⟩ := finite_angle_candidates_valid v hv
  constructor
  · intro i
    fin_cases i <;> dsimp [angleTableWeights] <;> omega
  · simp only [Fin.sum_univ_three, angleTableWeights, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val]
    omega

theorem Triangle.angle_weights_of_table_pair (S : Triangle) (v : ℕ × ℕ × ℕ)
    (hv : v ∈ finiteAngleCandidates)
    (ha : S.angle 0 = ((angleTablePair v).1 : ℝ) * Real.pi)
    (hb : S.angle 1 = ((angleTablePair v).2 : ℝ) * Real.pi) :
    ∀ i, S.angle i = (angleTableWeights v i : ℝ) * (Real.pi / v.1) := by
  obtain ⟨hN, _, hap, hab, hsum⟩ := finite_angle_candidates_valid v hv
  have hN' : (v.1 : ℝ) ≠ 0 := by exact_mod_cast (show v.1 ≠ 0 by omega)
  dsimp only [angleTablePair] at ha hb
  push_cast at ha hb
  intro i
  fin_cases i
  · change S.angle 0 = (v.2.1 : ℝ) * (Real.pi / v.1)
    rw [ha]
    ring
  · change S.angle 1 = (v.2.2 : ℝ) * (Real.pi / v.1)
    rw [hb]
    ring
  · change S.angle 2 = ((v.1 - v.2.1 - v.2.2 : ℕ) : ℝ) * (Real.pi / v.1)
    rw [Nat.cast_sub (show v.2.2 ≤ v.1 - v.2.1 by omega),
      Nat.cast_sub (show v.2.1 ≤ v.1 by omega)]
    have hs := S.angle_sum
    rw [ha, hb] at hs
    field_simp at hs ⊢
    nlinarith

namespace Tiling

theorem counterexample_ordered_finite_tile_angles {T : Triangle} {n : ℕ}
    (d : Tiling T n) (hn : ¬ IsSquare n) (hnot : ¬ EightCases T)
    (h01 : d.tile.angle 0 < d.tile.angle 1) (h12 : d.tile.angle 1 < d.tile.angle 2) :
    ∃ v ∈ finiteAngleCandidates,
      ∀ i, d.tile.angle i = (angleTableWeights v i : ℝ) * (Real.pi / v.1) := by
  obtain ⟨_, _, hP, hQ, hR, _, _, t, ht, he, hd⟩ :=
    d.counterexample_ordered_corner_data hn hnot h01 h12
  have hv := finite_angle_candidates_exhaustive _ _ _ hP hQ hR t ht
    (d.admissible_corner_data_of_counterexample hn hnot h01 h12 t ht he)
  obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hv
  have hc := d.corner_column_angle_sum
  rw [Fin.sum_univ_three] at hc
  obtain ⟨ha, hb⟩ := corner_pair_realizes _ _ _ d.tile.angle_sum _ _ _ hc t he hd
  rw [← heq] at ha hb
  exact ⟨v, hv, d.tile.angle_weights_of_table_pair v hv ha hb⟩

theorem counterexample_finite_tile_angles {T : Triangle} {n : ℕ}
    (d : Tiling T n) (hn : ¬ IsSquare n) (hnot : ¬ EightCases T) :
    ∃ e : Equiv.Perm (Fin 3), ∃ v ∈ finiteAngleCandidates,
      ∀ i, Triangle.angle (d.tile.reindex e) i =
        (angleTableWeights v i : ℝ) * (Real.pi / v.1) := by
  obtain ⟨e, h01, h12, _⟩ := d.counterexample_ordered_small_middle hn hnot
  obtain ⟨v, hv, hw⟩ := (d.reindexTile e).counterexample_ordered_finite_tile_angles
    hn hnot h01 h12
  exact ⟨e, v, hv, hw⟩

end Tiling
end Erdos633b
