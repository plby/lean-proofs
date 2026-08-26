import ErdosProblems.Erdos633b.CornerPartition
import ErdosProblems.Erdos633b.AnglePartition

/-! Corner angle sums and natural angle coefficients for arbitrary actual
congruent-triangle tilings. No classification assumption is used. -/

namespace Erdos633b

namespace Triangle

theorem angle_cornerProject_pair (T S : Triangle) (hST : S.support ⊆ T.support)
    (i j : Fin 3) (hO : S.points j = T.points i) :
    EuclideanGeometry.angle (T.cornerProject i (S.points (j + 1))) (T.points i)
      (T.cornerProject i (S.points (j + 2))) = S.angle j := by
  have hu := T.cornerScale_pos i (hST (S.vertex_mem_support (j + 1)))
    (T.corner_other_ne S i j (j + 1) hO ((by decide : ∀ j : Fin 3, j + 1 ≠ j) j))
  have hv := T.cornerScale_pos i (hST (S.vertex_mem_support (j + 2)))
    (T.corner_other_ne S i j (j + 2) hO ((by decide : ∀ j : Fin 3, j + 2 ≠ j) j))
  simp only [EuclideanGeometry.angle, cornerProject, AffineMap.homothety_apply, vadd_vsub]
  rw [InnerProductGeometry.angle_smul_left_of_pos _ _ (inv_pos.mpr hu),
    InnerProductGeometry.angle_smul_right_of_pos _ _ (inv_pos.mpr hv), ← hO]
  rfl

end Triangle

namespace Tiling

noncomputable instance {T : Triangle} {n : ℕ} (d : Tiling T n) (i : Fin 3) :
    Fintype (d.CornerPiece i) := Fintype.ofFinite _

theorem angle_eq_sum_cornerPieces {T : Triangle} {n : ℕ} (d : Tiling T n) (i : Fin 3) :
    T.angle i = ∑ e : d.CornerPiece i, d.tile.angle e.val.2 := by
  let A : d.CornerPiece i → Plane := fun e =>
    T.cornerProject i ((d.tile.move (d.place e.val.1)).points (e.val.2 + 1))
  let B : d.CornerPiece i → Plane := fun e =>
    T.cornerProject i ((d.tile.move (d.place e.val.1)).points (e.val.2 + 2))
  have hsub (e : d.CornerPiece i) : (d.tile.move (d.place e.val.1)).support ⊆ T.support := by
    rw [Triangle.support_move]
    exact d.piece_subset e.val.1
  have hAB (e : d.CornerPiece i) : A e ≠ B e :=
    T.cornerProject_pair_ne (d.tile.move (d.place e.val.1)) (hsub e) i e.val.2 e.property
  have hc : (⋃ e, segment ℝ (A e) (B e)) = T.edge i :=
    d.corner_sections_cover i
  have hd : Pairwise fun e f => Disjoint (openSegment ℝ (A e) (B e))
      (openSegment ℝ (A f) (B f)) := d.corner_sections_open_pairwise i
  have h := T.edge_partition_angle_sum i A B hAB hc hd
  have hangle (e : d.CornerPiece i) : EuclideanGeometry.angle (A e) (T.points i) (B e) =
      d.tile.angle e.val.2 := by
    exact (T.angle_cornerProject_pair (d.tile.move (d.place e.val.1)) (hsub e) i e.val.2
      e.property).trans (d.tile.angle_move (d.place e.val.1) e.val.2)
  simpa only [hangle] using h

/-- Number of incident tile corners of reference angle index `j`. -/
noncomputable def cornerAngleCount {T : Triangle} {n : ℕ} (d : Tiling T n)
    (i j : Fin 3) : ℕ := by
  classical
  exact (Finset.univ.filter (fun e : d.CornerPiece i => e.val.2 = j)).card

theorem angle_eq_sum_counts {T : Triangle} {n : ℕ} (d : Tiling T n) (i : Fin 3) :
    T.angle i = ∑ j : Fin 3, (d.cornerAngleCount i j : ℝ) * d.tile.angle j := by
  classical
  rw [d.angle_eq_sum_cornerPieces]
  rw [← Finset.sum_fiberwise' Finset.univ (fun e : d.CornerPiece i => e.val.2) d.tile.angle]
  simp only [Finset.sum_const, nsmul_eq_mul, cornerAngleCount]

theorem exists_angle_coefficients {T : Triangle} {n : ℕ} (d : Tiling T n) :
    ∃ m : Fin 3 → Fin 3 → ℕ,
      ∀ i, T.angle i = ∑ j : Fin 3, (m i j : ℝ) * d.tile.angle j :=
  ⟨d.cornerAngleCount, d.angle_eq_sum_counts⟩

theorem angle_eq_three_counts {T : Triangle} {n : ℕ} (d : Tiling T n) (i : Fin 3) :
    T.angle i = (d.cornerAngleCount i 0 : ℝ) * d.tile.angle 0 +
      (d.cornerAngleCount i 1 : ℝ) * d.tile.angle 1 +
      (d.cornerAngleCount i 2 : ℝ) * d.tile.angle 2 := by
  simpa only [Fin.sum_univ_three] using d.angle_eq_sum_counts i

end Tiling

end Erdos633b
