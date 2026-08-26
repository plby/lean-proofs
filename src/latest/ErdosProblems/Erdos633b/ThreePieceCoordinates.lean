import ErdosProblems.Erdos633b.CaseTwo
import ErdosProblems.Erdos633b.Median

/-! Explicit metric certificates for the three-piece 30-60-90 construction. -/

namespace Erdos633b.ThreePiece

theorem coordinate_dist_sq (x y u v : ℝ) :
    dist (!₂[x, y] : Plane) !₂[u, v] ^ 2 = (x - u) ^ 2 + (y - v) ^ 2 := by
  rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
  simp [Fin.sum_univ_two]

noncomputable def outer (d : ℝ) (hd : 0 < d) : Triangle where
  points := ![0, !₂[3, 0], !₂[0, d]]
  independent := TriquadraticCoordinates.normalized_independent 3 0 d (by norm_num) hd.ne'

noncomputable def reference (d : ℝ) (hd : 0 < d) : Triangle :=
  (outer d hd).edgeFirst (1 / 3) (by norm_num)

noncomputable def remaining (d : ℝ) (hd : 0 < d) : Triangle :=
  (outer d hd).edgeSecond (1 / 3) (by norm_num)

theorem reference_points (d : ℝ) (hd : 0 < d) :
    (reference d hd).points = ![!₂[0, d], 0, !₂[1, 0]] := by
  rw [reference, Triangle.edgeFirst_points]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [outer, Triangle.edgePoint_eq]
  all_goals rfl

theorem remaining_points (d : ℝ) (hd : 0 < d) :
    (remaining d hd).points = ![!₂[0, d], !₂[3, 0], !₂[1, 0]] := by
  rw [remaining, Triangle.edgeSecond_points]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [outer, Triangle.edgePoint_eq]
  all_goals rfl

theorem first_points (d : ℝ) (hd : 0 < d) :
    (remaining d hd).firstHalf.points = ![!₂[1, 0], !₂[0, d], !₂[3 / 2, d / 2]] := by
  rw [Triangle.firstHalf_points, remaining_points]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [midpoint_eq_smul_add, invOf_eq_inv]
  all_goals first | rfl | ring

theorem second_points (d : ℝ) (hd : 0 < d) :
    (remaining d hd).secondHalf.points = ![!₂[1, 0], !₂[3, 0], !₂[3 / 2, d / 2]] := by
  rw [Triangle.secondHalf_points, remaining_points]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [midpoint_eq_smul_add, invOf_eq_inv]
  all_goals first | rfl | ring

theorem side_sq_of_points (T : Triangle) (p : Fin 3 → Plane) (hp : T.points = p) (i : Fin 3) :
    T.side i ^ 2 = dist (p (i + 1)) (p (i + 2)) ^ 2 := by
  change dist (T.points (i + 1)) (T.points (i + 2)) ^ 2 = _
  rw [hp]

theorem outer_side_sq (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3) (i : Fin 3) :
    (outer d hd).side i ^ 2 = ![12, 3, 9] i := by
  rw [side_sq_of_points (outer d hd) ![0, !₂[3, 0], !₂[0, d]] rfl]
  have hz : (0 : Plane) = !₂[0, 0] := by ext j; fin_cases j <;> rfl
  simp only [hz]
  fin_cases i
  · change dist (!₂[3, 0] : Plane) !₂[0, d] ^ 2 = 12
    rw [coordinate_dist_sq]
    nlinarith
  · change dist (!₂[0, d] : Plane) !₂[0, 0] ^ 2 = 3
    rw [coordinate_dist_sq]
    nlinarith
  · change dist (!₂[0, 0] : Plane) !₂[3, 0] ^ 2 = 9
    rw [coordinate_dist_sq]
    norm_num

theorem reference_side_sq (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3) (i : Fin 3) :
    (reference d hd).side i ^ 2 = ![1, 4, 3] i := by
  rw [side_sq_of_points _ _ (reference_points d hd)]
  have hz : (0 : Plane) = !₂[0, 0] := by ext j; fin_cases j <;> rfl
  simp only [hz]
  fin_cases i
  · change dist (!₂[0, 0] : Plane) !₂[1, 0] ^ 2 = 1
    rw [coordinate_dist_sq]
    norm_num
  · change dist (!₂[1, 0] : Plane) !₂[0, d] ^ 2 = 4
    rw [coordinate_dist_sq]
    nlinarith
  · change dist (!₂[0, d] : Plane) !₂[0, 0] ^ 2 = 3
    rw [coordinate_dist_sq]
    nlinarith

theorem first_side_sq (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3) (i : Fin 3) :
    (remaining d hd).firstHalf.side i ^ 2 = ![3, 1, 4] i := by
  rw [side_sq_of_points _ _ (first_points d hd)]
  fin_cases i
  · change dist (!₂[0, d] : Plane) !₂[3 / 2, d / 2] ^ 2 = 3
    rw [coordinate_dist_sq]
    nlinarith
  · change dist (!₂[3 / 2, d / 2] : Plane) !₂[1, 0] ^ 2 = 1
    rw [coordinate_dist_sq]
    nlinarith
  · change dist (!₂[1, 0] : Plane) !₂[0, d] ^ 2 = 4
    rw [coordinate_dist_sq]
    nlinarith

theorem second_side_sq (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3) (i : Fin 3) :
    (remaining d hd).secondHalf.side i ^ 2 = ![3, 1, 4] i := by
  rw [side_sq_of_points _ _ (second_points d hd)]
  fin_cases i
  · change dist (!₂[3, 0] : Plane) !₂[3 / 2, d / 2] ^ 2 = 3
    rw [coordinate_dist_sq]
    nlinarith
  · change dist (!₂[3 / 2, d / 2] : Plane) !₂[1, 0] ^ 2 = 1
    rw [coordinate_dist_sq]
    nlinarith
  · change dist (!₂[1, 0] : Plane) !₂[3, 0] ^ 2 = 4
    rw [coordinate_dist_sq]
    norm_num

end Erdos633b.ThreePiece
