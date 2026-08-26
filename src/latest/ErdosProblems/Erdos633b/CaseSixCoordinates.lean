import ErdosProblems.Erdos633b.EdgeExtension
import ErdosProblems.Erdos633b.TriquadraticAngles
import ErdosProblems.Erdos633b.CaseTwo

/-! A positive two-piece extension replaces the case-(6) construction with negative row counts. -/

namespace Erdos633b.CaseSixCoordinates

open TriquadraticCoordinates

noncomputable def tip (c s : ℝ) : Plane := (3 - s ^ 2) • bigC c s

noncomputable def base (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1)
    (hd : 0 < d) : Triangle :=
  (TriquadraticCoordinates.outer c s d hc hs hs1 hd).reindex (Equiv.swap 0 1)

theorem base_points (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1) (hd : 0 < d) :
    (base c s d hc hs hs1 hd).points = ![bigB c s d, 0, bigC c s] := by
  funext i
  fin_cases i <;> rfl

theorem extendedPoint_eq (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1) (hd : 0 < d) :
    (base c s d hc hs hs1 hd).extendedPoint (2 - s ^ 2) = tip c s := by
  rw [Triangle.extendedPoint, base_points]
  change (1 + (2 - s ^ 2)) • bigC c s - (2 - s ^ 2) • (0 : Plane) = (3 - s ^ 2) • bigC c s
  rw [smul_zero, sub_zero]
  congr 1
  ring

noncomputable def outer (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1)
    (hd : 0 < d) : Triangle :=
  (base c s d hc hs hs1 hd).edgeExtension (2 - s ^ 2) (parameter_denominator_pos s hs hs1).2

noncomputable def attached (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1)
    (hd : 0 < d) : Triangle :=
  (outer c s d hc hs hs1 hd).edgeSecond (1 / (1 + (2 - s ^ 2)))
    (Triangle.extension_weight_lt_one _ (parameter_denominator_pos s hs hs1).2)

theorem outer_points (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1) (hd : 0 < d) :
    (outer c s d hc hs hs1 hd).points = ![0, tip c s, bigB c s d] := by
  rw [outer, Triangle.edgeExtension_points, extendedPoint_eq, base_points]
  rfl

theorem attached_points (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1) (hd : 0 < d) :
    (attached c s d hc hs hs1 hd).points = ![bigB c s d, tip c s, bigC c s] := by
  rw [attached, outer, Triangle.edgeExtension_second_points, extendedPoint_eq, base_points]
  rfl

theorem norm_bigC (c s : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1) :
    ‖bigC c s‖ = c ^ 2 * (1 - s ^ 2) := by
  have hv : bigC c s = (c ^ 2 * (1 - s ^ 2)) • (!₂[1, 0] : Plane) := by
    ext i
    fin_cases i <;> simp [bigC]
  rw [hv, norm_smul, Real.norm_of_nonneg
    (mul_pos (sq_pos_of_pos hc) (parameter_denominator_pos s hs hs1).1).le, norm_e, mul_one]

theorem bigB_sub_bigC (c s d : ℝ) :
    bigB c s d - bigC c s = (c ^ 2 * s * (2 - s ^ 2)) • (!₂[-s / 2, d / 2] : Plane) := by
  ext i
  fin_cases i <;> simp [bigB, bigC, w] <;> ring

theorem bigB_sub_tip (c s d : ℝ) :
    bigB c s d - tip c s = (c ^ 2 * (2 - s ^ 2)) • (!₂[-1 + s ^ 2 / 2, s * d / 2] : Plane) := by
  ext i
  fin_cases i <;> simp [bigB, bigC, tip, w] <;> ring

theorem norm_reflected_z (s d : ℝ) (he : d ^ 2 = 4 - s ^ 2) :
    ‖(!₂[-1 + s ^ 2 / 2, s * d / 2] : Plane)‖ = 1 := by
  have hh : ‖(!₂[-1 + s ^ 2 / 2, s * d / 2] : Plane)‖ ^ 2 = 1 := by
    simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    linear_combination (s ^ 2 / 4) * he
  nlinarith [norm_nonneg (!₂[-1 + s ^ 2 / 2, s * d / 2] : Plane)]

theorem attached_sides (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1)
    (hd : 0 < d) (he : d ^ 2 = 4 - s ^ 2) (i : Fin 3) :
    (attached c s d hc hs hs1 hd).side i =
      (c * (2 - s ^ 2)) * ![c * (1 - s ^ 2), c * s, c] i := by
  let V := attached c s d hc hs hs1 hd
  have ht := parameter_denominator_pos s hs hs1
  fin_cases i
  · change dist (V.points 1) (V.points 2) = c * (2 - s ^ 2) * (c * (1 - s ^ 2))
    rw [attached_points]
    change dist (tip c s) (bigC c s) = _
    have hv : tip c s - bigC c s = (2 - s ^ 2) • bigC c s := by unfold tip; module
    rw [dist_eq_norm, hv, norm_smul, Real.norm_of_nonneg ht.2.le, norm_bigC c s hc hs hs1]
    ring
  · change dist (V.points 2) (V.points 0) = c * (2 - s ^ 2) * (c * s)
    rw [attached_points]
    change dist (bigC c s) (bigB c s d) = _
    rw [dist_comm, dist_eq_norm, bigB_sub_bigC, norm_smul,
      Real.norm_of_nonneg (mul_pos (mul_pos (sq_pos_of_pos hc) hs) ht.2).le,
      norm_turn_e s d he]
    ring
  · change dist (V.points 0) (V.points 1) = c * (2 - s ^ 2) * c
    rw [attached_points]
    change dist (bigB c s d) (tip c s) = _
    rw [dist_eq_norm, bigB_sub_tip, norm_smul,
      Real.norm_of_nonneg (mul_pos (sq_pos_of_pos hc) ht.2).le, norm_reflected_z s d he]
    ring

end Erdos633b.CaseSixCoordinates
