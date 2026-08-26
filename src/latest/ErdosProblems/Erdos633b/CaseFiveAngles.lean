import ErdosProblems.Erdos633b.CaseFiveCoordinates
import ErdosProblems.Erdos633b.CaseTwo

/-! Exact angle matching for the final case-(5) attachment. -/

namespace Erdos633b

theorem Triangle.angles_of_scaled_sides (R S : Triangle) (k : ℝ) (hk : 0 < k)
    (hs : ∀ i, S.side i = k * R.side i) (i : Fin 3) : S.angle i = R.angle i := by
  let U := R.dilate k hk.ne'
  have hd (j : Fin 3) : U.side j = S.side j := by
    rw [Triangle.side_dilate, abs_of_pos hk]
    exact (hs j).symm
  have hdist := U.distances_of_sides S hd
  have heq := congrArg (fun T : Triangle => T.angle i) (U.move_vertexIsometry S hdist)
  rw [Triangle.angle_move, Triangle.angle_dilate] at heq
  exact heq.symm

namespace CaseFiveCoordinates

open Sixty

theorem attached_angle_one (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3) (a b c m : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hm : 0 < m)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    (attached d hd a b c m ha hb hc hm).angle 1 =
      (groupTwoReference d hd a b ha hb).angle 1 := by
  let R := groupTwoReference d hd a b ha hb
  let R' : Triangle := R.reindex (Equiv.swap 0 2)
  let V := attached d hd a b c m ha hb hc hm
  have hs (i : Fin 3) : V.side i = (m * (a + 2 * b)) * R'.side i := by
    rw [attached_sides d hd he a b c m ha hb hc hm hrel, Triangle.side_reindex,
      reference_sides d hd he a b c ha hb hc hrel]
    congr 1
    fin_cases i <;> rfl
  have hh := R'.angles_of_scaled_sides V (m * (a + 2 * b)) (by positivity) hs 1
  rw [Triangle.angle_reindex] at hh
  exact hh

theorem outer_angles (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3) (a b c m : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hm : 0 < m)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    let U := outer d hd a b c m ha hb hc hm
    let R := groupTwoReference d hd a b ha hb
    U.angle 0 = 2 * R.angle 1 ∧ U.angle 1 = R.angle 1 ∧ U.angle 2 = 3 * R.angle 2 := by
  let S := DoubledCoordinates.outer d hd a b c m ha hb hc hm
  let U := outer d hd a b c m ha hb hc hm
  let R := groupTwoReference d hd a b ha hb
  have h0 : U.angle 0 = 2 * R.angle 1 :=
    (S.edgeExtension_angle_zero _ (extensionRatio_pos a b ha hb)).trans
      (DoubledCoordinates.outer_angle_one d hd he a b c m ha hb hc hm hrel)
  have h1 : U.angle 1 = R.angle 1 :=
    (S.edgeExtension_angle_one _ (extensionRatio_pos a b ha hb)).trans
      (attached_angle_one d hd he a b c m ha hb hc hm hrel)
  have hR0 : R.angle 0 = 2 * Real.pi / 3 := reference_angle_zero d hd he a b c ha hb hc hrel
  refine ⟨h0, h1, ?_⟩
  change U.angle 2 = 3 * R.angle 2
  linarith [U.angle_sum, R.angle_sum]

end CaseFiveCoordinates
end Erdos633b
