import ErdosProblems.Erdos633b.CaseSixCoordinates
import ErdosProblems.Erdos633b.GroupOneMetric
import ErdosProblems.Erdos633b.CaseFiveAngles

/-! The positive extension has exactly the angle relation and parameter required in case (6). -/

namespace Erdos633b.CaseSixCoordinates

open TriquadraticCoordinates

theorem attached_angle_one (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1)
    (hd : 0 < d) (he : d ^ 2 = 4 - s ^ 2) :
    (attached c s d hc hs hs1 hd).angle 1 = (reference c s d hc hs hs1 hd).angle 0 := by
  let R := reference c s d hc hs hs1 hd
  let R' : Triangle := R.reindex (Equiv.swap 0 1)
  let V := attached c s d hc hs hs1 hd
  have hside (i : Fin 3) : V.side i = (c * (2 - s ^ 2)) * R'.side i := by
    rw [attached_sides c s d hc hs hs1 hd he, Triangle.side_reindex,
      reference_sides c s d hc hs hs1 hd he]
    congr 1
    fin_cases i <;> rfl
  have hh := R'.angles_of_scaled_sides V (c * (2 - s ^ 2))
    (mul_pos hc (parameter_denominator_pos s hs hs1).2) hside 1
  rw [Triangle.angle_reindex] at hh
  exact hh

theorem outer_angle_zero (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1) (hd : 0 < d) :
    (outer c s d hc hs hs1 hd).angle 0 =
      (TriquadraticCoordinates.outer c s d hc hs hs1 hd).angle 0 := by
  rw [outer, Triangle.edgeExtension_angle_zero, base, Triangle.angle_reindex]
  rfl

theorem outer_angle_relations (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1)
    (hd : 0 < d) (he : d ^ 2 = 4 - s ^ 2) :
    (outer c s d hc hs hs1 hd).angle 0 = 2 * (outer c s d hc hs hs1 hd).angle 1 ∧
      2 * Real.sin ((outer c s d hc hs hs1 hd).angle 1 / 2) = s := by
  let U := outer c s d hc hs hs1 hd
  let S := base c s d hc hs hs1 hd
  let T := TriquadraticCoordinates.outer c s d hc hs hs1 hd
  let R := reference c s d hc hs hs1 hd
  have hu1 : U.angle 1 = R.angle 0 :=
    (S.edgeExtension_angle_one _ (parameter_denominator_pos s hs hs1).2).trans
      (attached_angle_one c s d hc hs hs1 hd he)
  have hu0 : U.angle 0 = T.angle 0 := outer_angle_zero c s d hc hs hs1 hd
  have hT0 : T.angle 0 = 2 * R.angle 0 := outer_angle_zero_eq_twice_reference c s d hc hs hs1 hd he
  have hrel : U.angle 0 = 2 * U.angle 1 := by linarith
  refine ⟨hrel, ?_⟩
  have hhalf : U.angle 1 / 2 = T.angle 0 / 4 := by linarith
  rw [hhalf]
  exact (TriquadraticCoordinates.outer_angle_relations c s d hc hs hs1 hd he).2

end Erdos633b.CaseSixCoordinates
