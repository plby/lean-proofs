import ErdosProblems.Erdos633.SignedReptile
import ErdosProblems.Erdos633.TilingRelabelCounts

/-!
# A missing outer angle in an irrational nonsquare reptiling is right

The actual angle ledger bounds the two surviving outer counts by three. The
signed boundary obstruction forces both counts to be even, hence both are two.
The missing reference angle is therefore pi/2. No homogeneous relation lattice
or checkerboard-coloring assumption is required.
-/

namespace Erdos633

open scoped BigOperators

theorem CongruentTiling.aligned_missing_outer_counts_positive
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hind : IntegerIndependentAngles R.angleA R.angleB) (hg : T.outerCornerCount 2 = 0)
    (hA : P.angleA = R.angleA) (hB : P.angleB = R.angleB) :
    0 < T.outerCornerCount 0 ∧ 0 < T.outerCornerCount 1 := by
  constructor
  · by_contra ha
    have ha0 : T.outerCornerCount 0 = 0 := by omega
    have h := T.outer_angle_count_identity 0
    have hz0 := T.cornerCount_eq_zero_of_outer_eq_zero 0 0 ha0
    have hz2 := T.cornerCount_eq_zero_of_outer_eq_zero 0 2 hg
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
    change (T.cornerCount (P.vertex 0) 0 : ℝ) * R.angleA +
      ((T.cornerCount (P.vertex 0) 1 : ℝ) * R.angleB +
        (T.cornerCount (P.vertex 0) 2 : ℝ) * R.angleC) = P.angleA at h
    rw [hz0, hz2] at h
    simp only [Nat.cast_zero, zero_mul, zero_add, add_zero, hA] at h
    have hbad := (hind 1 (-(T.cornerCount (P.vertex 0) 1 : ℤ)) (by push_cast; linarith)).1
    norm_num at hbad
  · by_contra hb
    have hb0 : T.outerCornerCount 1 = 0 := by omega
    have h := T.outer_angle_count_identity 1
    have hz1 := T.cornerCount_eq_zero_of_outer_eq_zero 1 1 hb0
    have hz2 := T.cornerCount_eq_zero_of_outer_eq_zero 1 2 hg
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
    change (T.cornerCount (P.vertex 1) 0 : ℝ) * R.angleA +
      ((T.cornerCount (P.vertex 1) 1 : ℝ) * R.angleB +
        (T.cornerCount (P.vertex 1) 2 : ℝ) * R.angleC) = P.angleB at h
    rw [hz1, hz2] at h
    simp only [Nat.cast_zero, zero_mul, add_zero, hB] at h
    have hbad := (hind (-(T.cornerCount (P.vertex 1) 0 : ℤ)) 1 (by push_cast; linarith)).2
    norm_num at hbad

theorem CongruentTiling.missing_angle_right_of_nonsquare_aligned_reptile
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hN : ¬ IsSquare N) (hR : ¬ R.CommensurableAngles)
    (hg : T.outerCornerCount 2 = 0)
    (hA : P.angleA = R.angleA) (hB : P.angleB = R.angleB) : R.angleC = Real.pi / 2 := by
  have hind : IntegerIndependentAngles R.angleA R.angleB := by
    simpa [Triangle.cornerAngle] using T.independent_angles_of_missing (Equiv.refl _) hR
      (by simpa using hg)
  obtain ⟨ha, hb⟩ := T.aligned_missing_outer_counts_positive hind hg hA hB
  obtain ⟨ha3, hb3⟩ := T.outer_counts_le_three_of_missing hind ha hb hg
  let πc : ℤ × ℤ := ((T.outerCornerCount 0 : ℤ), (T.outerCornerCount 1 : ℤ))
  have hπ : Real.pi = angleFromCoordinates R.angleA R.angleB πc := by
    have h := T.outer_angle_total
    simpa [πc, angleFromCoordinates, Triangle.cornerAngle, Fin.sum_univ_succ, hg] using h.symm
  have ha2 : T.outerCornerCount 0 = 2 := by
    by_contra hne
    have hc : T.outerCornerCount 0 = 1 ∨ T.outerCornerCount 0 = 3 := by omega
    have hchar : directionSign 1 0 πc = -1 := by
      rcases hc with hc | hc <;> norm_num [directionSign, πc, hc]
    exact hN (T.signed_aligned_reptile_isSquare hind πc hπ 1 0 hchar hA hB)
  have hb2 : T.outerCornerCount 1 = 2 := by
    by_contra hne
    have hc : T.outerCornerCount 1 = 1 ∨ T.outerCornerCount 1 = 3 := by omega
    have hchar : directionSign 0 1 πc = -1 := by
      rcases hc with hc | hc <;> norm_num [directionSign, πc, hc]
    exact hN (T.signed_aligned_reptile_isSquare hind πc hπ 0 1 hchar hA hB)
  have hsum : 2 * R.angleA + 2 * R.angleB = Real.pi := by
    simpa [πc, angleFromCoordinates, ha2, hb2] using hπ.symm
  linarith [R.angle_sum]

end Erdos633
